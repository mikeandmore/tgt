/*
 * Synchronous I/O file backing store routine
 *
 * Copyright (C) 2006-2007 FUJITA Tomonori <tomof@acm.org>
 * Copyright (C) 2006-2007 Mike Christie <michaelc@cs.wisc.edu>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, version 2 of the
 * License.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
 * 02110-1301 USA
 */
#define _XOPEN_SOURCE 600

#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>

#include <linux/fs.h>
#include <sys/epoll.h>

#include "list.h"
#include "util.h"
#include "tgtd.h"
#include "scsi.h"
#include "spc.h"
#include "bs_thread.h"

#include "../../lru2cache.h"
#include "../../device.h"
#include "../../bitmap.h"
#include "../../btree.h"
#include "../../sync-thread.h"

static void set_medium_error(int *result, uint8_t *key, uint16_t *asc)
{
	*result = SAM_STAT_CHECK_CONDITION;
	*key = MEDIUM_ERROR;
	*asc = ASC_READ_ERROR;
}

static void bs_sync_sync_range(struct scsi_cmd *cmd, uint32_t length,
			       int *result, uint8_t *key, uint16_t *asc)
{
	int ret;

	ret = fdatasync(cmd->dev->fd);
	if (ret)
		set_medium_error(result, key, asc);
}

static struct cache *cache;
static struct btree *clean_btree, *dirty_btree;
static struct bitmap *bitmap;
struct sync_thread_info info;

#define PRI_DEV 1
#define CACHE_DEV 2
#define CACHE_DEV_PATH "/dev/sdb"

static inline int check_alignment(uint64_t length, uint64_t offset)
{
	if (offset % 512 == 0 && length % 512 == 0) {
		return 1;
	} else {
		eprintf("unaligned write\n");
		return 0;
	}
}

static int bs_pstor_pread(int fd, void *buffer, uint64_t length,
			  uint64_t offset)
{
	unsigned char *base_ptr = buffer;
	unsigned char *end_ptr = base_ptr + length;
	unsigned char *ptr = base_ptr;
	void *extra_buffer = NULL;
	blkptr_t blknr = offset;

	if (fd != dev_getfd(cache->primary_dev_id))
		return pread64(fd, buffer, length, offset);

	if (!check_alignment(length, offset))
		return -1;

	while (ptr < end_ptr) {
		blkptr_t rem = blknr % BLK_SIZE;
		uint64_t rem_length = BLK_SIZE - rem;

		if (length < rem_length) {
			rem_length = length;
		}

		if (rem != 0 || rem_length < BLK_SIZE) {
			blknr -= rem;
			extra_buffer = buffer_alloc();
			cache_pstor_read(cache, extra_buffer, blknr);
			memcpy(ptr, extra_buffer + rem, rem_length);
			buffer_free(extra_buffer);
		} else {
			cache_pstor_read(cache, ptr, blknr);
		}
		ptr += rem_length;
		blknr += BLK_SIZE;
		length -= rem_length;
	}
	return ptr - base_ptr;
}

static int bs_pstor_pwrite(int fd, const void *buffer, uint64_t length,
			   uint64_t offset)
{
	const unsigned char *base_ptr = buffer;
	const unsigned char *ptr = base_ptr;
	blkptr_t blknr = offset;

	if (fd != dev_getfd(cache->primary_dev_id))
		return pwrite64(fd, buffer, length, offset);

	if (!check_alignment(length, offset))
		return -1;

	while (ptr < base_ptr + length) {
		cache_pstor_write(cache, ptr, blknr);
		ptr += BLK_SIZE;
		blknr += BLK_SIZE;
	}
	return length;
}

static void bs_rdwr_request(struct scsi_cmd *cmd)
{
	int ret, fd = cmd->dev->fd;
	uint32_t length;
	int result = SAM_STAT_GOOD;
	uint8_t key;
	uint16_t asc;
	uint32_t info = 0;
	char *tmpbuf;
	size_t blocksize;
	uint64_t offset = cmd->offset;
	uint32_t tl     = cmd->tl;
	int do_verify = 0;
	int i;
	char *ptr;

	ret = length = 0;
	key = asc = 0;

	switch (cmd->scb[0])
	{
	case ORWRITE_16:
		dprintf("not aware for ORWRITE\n");
		length = scsi_get_out_length(cmd);

		tmpbuf = malloc(length);
		if (!tmpbuf) {
			result = SAM_STAT_CHECK_CONDITION;
			key = HARDWARE_ERROR;
			asc = ASC_INTERNAL_TGT_FAILURE;
			break;
		}

		ret = pread64(fd, tmpbuf, length, offset);

		if (ret != length) {
			set_medium_error(&result, &key, &asc);
			free(tmpbuf);
			break;
		}

		ptr = scsi_get_out_buffer(cmd);
		for (i = 0; i < length; i++)
			ptr[i] |= tmpbuf[i];

		free(tmpbuf);

		goto write;
	case COMPARE_AND_WRITE:
		dprintf("not aware of COMPARE_AND_WRITE\n");
		length = scsi_get_out_length(cmd);

		tmpbuf = malloc(length);
		if (!tmpbuf) {
			result = SAM_STAT_CHECK_CONDITION;
			key = HARDWARE_ERROR;
			asc = ASC_INTERNAL_TGT_FAILURE;
			break;
		}

		ret = pread64(fd, tmpbuf, length, offset);

		if (ret != length) {
			set_medium_error(&result, &key, &asc);
			free(tmpbuf);
			break;
		}

		if (memcmp(scsi_get_out_buffer(cmd), tmpbuf, length)) {
			uint32_t pos = 0;
			char *spos = scsi_get_out_buffer(cmd);
			char *dpos = tmpbuf;

			/*
			 * Data differed, this is assumed to be 'rare'
			 * so use a much more expensive byte-by-byte
			 * comparasion to find out at which offset the
			 * data differs.
			 */
			for (pos = 0; pos < length && *spos++ == *dpos++;
			     pos++)
				;
			info = pos;
			result = SAM_STAT_CHECK_CONDITION;
			key = MISCOMPARE;
			asc = ASC_MISCOMPARE_DURING_VERIFY_OPERATION;
			free(tmpbuf);
			break;
		}

		if (cmd->scb[1] & 0x10)
			posix_fadvise(fd, offset, length,
				      POSIX_FADV_NOREUSE);

		free(tmpbuf);

		goto write;
	case SYNCHRONIZE_CACHE:
	case SYNCHRONIZE_CACHE_16:
		/* TODO */
		dprintf("SYNC\n");
		length = (cmd->scb[0] == SYNCHRONIZE_CACHE) ? 0 : 0;

		if (cmd->scb[1] & 0x2) {
			result = SAM_STAT_CHECK_CONDITION;
			key = ILLEGAL_REQUEST;
			asc = ASC_INVALID_FIELD_IN_CDB;
		} else
			bs_sync_sync_range(cmd, length, &result, &key, &asc);
		break;
	case WRITE_VERIFY:
	case WRITE_VERIFY_12:
	case WRITE_VERIFY_16:
		do_verify = 1;
	case WRITE_6:
	case WRITE_10:
	case WRITE_12:
	case WRITE_16:
write:
		length = scsi_get_out_length(cmd);
		/*
		ret = pwrite64(fd, scsi_get_out_buffer(cmd), length,
			       offset);
		*/
		ret = bs_pstor_pwrite(fd, scsi_get_out_buffer(cmd), length,
				      offset);
		if (ret == length) {
			struct mode_pg *pg;

			/*
			 * it would be better not to access to pg
			 * directy.
			 */
			pg = find_mode_page(cmd->dev, 0x08, 0);
			if (pg == NULL) {
				result = SAM_STAT_CHECK_CONDITION;
				key = ILLEGAL_REQUEST;
				asc = ASC_INVALID_FIELD_IN_CDB;
				break;
			}
			if (((cmd->scb[0] != WRITE_6) && (cmd->scb[1] & 0x8)) ||
			    !(pg->mode_data[0] & 0x04))
				bs_sync_sync_range(cmd, length, &result, &key,
						   &asc);
		} else
			set_medium_error(&result, &key, &asc);

		if ((cmd->scb[0] != WRITE_6) && (cmd->scb[1] & 0x10))
			posix_fadvise(fd, offset, length,
				      POSIX_FADV_NOREUSE);
		if (do_verify)
			goto verify;
		break;
	case WRITE_SAME:
	case WRITE_SAME_16:
		dprintf("not aware of WRITE_SAME\n");
		/* WRITE_SAME used to punch hole in file */
		if (cmd->scb[1] & 0x08) {
			ret = unmap_file_region(fd, offset, tl);
			if (ret != 0) {
				eprintf("Failed to punch hole for WRITE_SAME"
					" command\n");
				result = SAM_STAT_CHECK_CONDITION;
				key = HARDWARE_ERROR;
				asc = ASC_INTERNAL_TGT_FAILURE;
				break;
			}
			break;
		}
		while (tl > 0) {
			blocksize = 1 << cmd->dev->blk_shift;
			tmpbuf = scsi_get_out_buffer(cmd);

			switch(cmd->scb[1] & 0x06) {
			case 0x02: /* PBDATA==0 LBDATA==1 */
				put_unaligned_be32(offset, tmpbuf);
				break;
			case 0x04: /* PBDATA==1 LBDATA==0 */
				/* physical sector format */
				put_unaligned_be64(offset, tmpbuf);
				break;
			}

			ret = pwrite64(fd, tmpbuf, blocksize, offset);
			if (ret != blocksize)
				set_medium_error(&result, &key, &asc);

			offset += blocksize;
			tl     -= blocksize;
		}
		break;
	case READ_6:
	case READ_10:
	case READ_12:
	case READ_16:
		length = scsi_get_in_length(cmd);
		/*
		ret = pread64(fd, scsi_get_in_buffer(cmd), length,
			      offset);
		*/
		ret = bs_pstor_pread(fd, scsi_get_in_buffer(cmd), length,
				     offset);

		if (ret != length)
			set_medium_error(&result, &key, &asc);

		if ((cmd->scb[0] != READ_6) && (cmd->scb[1] & 0x10))
			posix_fadvise(fd, offset, length,
				      POSIX_FADV_NOREUSE);

		break;
	case PRE_FETCH_10:
	case PRE_FETCH_16:
		ret = posix_fadvise(fd, offset, cmd->tl,
				POSIX_FADV_WILLNEED);

		if (ret != 0)
			set_medium_error(&result, &key, &asc);
		break;
	case VERIFY_10:
	case VERIFY_12:
	case VERIFY_16:
verify:
		length = scsi_get_out_length(cmd);

		tmpbuf = malloc(length);
		if (!tmpbuf) {
			result = SAM_STAT_CHECK_CONDITION;
			key = HARDWARE_ERROR;
			asc = ASC_INTERNAL_TGT_FAILURE;
			break;
		}

		ret = pread64(fd, tmpbuf, length, offset);

		if (ret != length)
			set_medium_error(&result, &key, &asc);
		else if (memcmp(scsi_get_out_buffer(cmd), tmpbuf, length)) {
			result = SAM_STAT_CHECK_CONDITION;
			key = MISCOMPARE;
			asc = ASC_MISCOMPARE_DURING_VERIFY_OPERATION;
		}

		if (cmd->scb[1] & 0x10)
			posix_fadvise(fd, offset, length,
				      POSIX_FADV_NOREUSE);

		free(tmpbuf);
		break;
	case UNMAP:
		dprintf("not aware of UNMAP\n");
		if (!cmd->dev->attrs.thinprovisioning) {
			result = SAM_STAT_CHECK_CONDITION;
			key = ILLEGAL_REQUEST;
			asc = ASC_INVALID_FIELD_IN_CDB;
			break;
		}

		length = scsi_get_out_length(cmd);
		tmpbuf = scsi_get_out_buffer(cmd);

		if (length < 8)
			break;

		length -= 8;
		tmpbuf += 8;

		while (length >= 16) {
			offset = get_unaligned_be64(&tmpbuf[0]);
			offset = offset << cmd->dev->blk_shift;

			tl = get_unaligned_be32(&tmpbuf[8]);
			tl = tl << cmd->dev->blk_shift;

			if (offset + tl > cmd->dev->size) {
				eprintf("UNMAP beyond EOF\n");
				result = SAM_STAT_CHECK_CONDITION;
				key = ILLEGAL_REQUEST;
				asc = ASC_LBA_OUT_OF_RANGE;
				break;
			}

			if (tl > 0) {
				if (unmap_file_region(fd, offset, tl) != 0) {
					eprintf("Failed to punch hole for"
						" UNMAP at offset:%" PRIu64
						" length:%d\n",
						offset, tl);
					result = SAM_STAT_CHECK_CONDITION;
					key = HARDWARE_ERROR;
					asc = ASC_INTERNAL_TGT_FAILURE;
					break;
				}
			}

			length -= 16;
			tmpbuf += 16;
		}
		break;
	default:
		break;
	}

	dprintf("io done %p %x %d %u\n", cmd, cmd->scb[0], ret, length);

	scsi_set_result(cmd, result);

	if (result != SAM_STAT_GOOD) {
		eprintf("io error %p %x %d %d %" PRIu64 ", %m\n",
			cmd, cmd->scb[0], ret, length, offset);
		sense_data_build(cmd, key, asc);
	}
}

static int bs_rdwr_open(struct scsi_lu *lu, char *path, int *fd, uint64_t *size)
{
	uint32_t blksize = 0;

	*fd = backed_file_open(path, O_RDWR|O_LARGEFILE|lu->bsoflags, size,
				&blksize);
	/* If we get access denied, try opening the file in readonly mode */
	if (*fd == -1 && (errno == EACCES || errno == EROFS)) {
		*fd = backed_file_open(path, O_RDONLY|O_LARGEFILE|lu->bsoflags,
				       size, &blksize);
		lu->attrs.readonly = 1;
	}
	if (*fd < 0)
		return *fd;

	if (!lu->attrs.no_auto_lbppbe)
		update_lbppbe(lu, blksize);

	return 0;
}

static void bs_rdwr_close(struct scsi_lu *lu)
{
	close(lu->fd);
}

static int bs_pstor_open(struct scsi_lu *lu, char *path, int *fd,
			 uint64_t *size)
{
	blkptr_t nrblks = 0;
	init_device(O_RDWR | O_LARGEFILE | lu->bsoflags);
	fprintf(stderr, "setting up %s\n", path);
	if (dev_open(CACHE_DEV_PATH, CACHE_DEV) != DEV_READY
	    || dev_open(path, PRI_DEV) != DEV_READY) {
		perror("open");
		return -1;
	}
	*size = dev_total_size(PRI_DEV);
	nrblks = *size / BLK_SIZE;

	/* setup the cache object */
	dprintf("device size %llu\n", *size);
	bitmap = bitmap_new(nrblks);
	clean_btree = btree_mem_new();
	dirty_btree = btree_mem_new();
	sync_thread_info_init(&info, 64, 128);
	dprintf("creating cache object\n");
	cache = cache_new(nrblks, clean_btree, dirty_btree, bitmap, &info,
			  CACHE_DEV, PRI_DEV);
	sync_thread_start_worker(&info);

	if (*size == 0) {
		return -1;
	}
	*fd = dev_getfd(PRI_DEV);
	if (!lu->attrs.no_auto_lbppbe)
		update_lbppbe(lu, BLK_SIZE); // set to 4K all the time
	return 0;
}

static void bs_pstor_close(struct scsi_lu *lu)
{
	dev_close(PRI_DEV);
	dev_close(CACHE_DEV);
}

int nr_iothreads = 16;

static tgtadm_err bs_rdwr_init(struct scsi_lu *lu)
{
	struct bs_thread_info *info = BS_THREAD_I(lu);

	return bs_thread_open(info, bs_rdwr_request, nr_iothreads);
}

static void bs_rdwr_exit(struct scsi_lu *lu)
{
	struct bs_thread_info *info = BS_THREAD_I(lu);

	bs_thread_close(info);
}

static struct backingstore_template rdwr_bst = {
	.bs_name		= "rdwr",
	.bs_datasize		= sizeof(struct bs_thread_info),
	.bs_open		= bs_pstor_open,
	.bs_close		= bs_pstor_close,
	.bs_init		= bs_rdwr_init,
	.bs_exit		= bs_rdwr_exit,
	.bs_cmd_submit		= bs_thread_cmd_submit,
	.bs_oflags_supported    = O_SYNC | O_DIRECT,
};

__attribute__((constructor)) static void bs_rdwr_constructor(void)
{
	register_backingstore_template(&rdwr_bst);
}
