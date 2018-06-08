/**
 * @file snapshot-api.h
 * @author rohanseh
 * @brief Interface header for cloudfs snapshots.
 * @date 03/22/2015
 */

#ifndef _SNAPSHOTAPI_H
#define _SNAPSHOTAPI_H

#include <sys/ioctl.h>

/**
 * defines the maximum number of snapshots cloudfs supports.
 */
#define CLOUDFS_MAX_NUM_SNAPSHOTS 8

/**
 * Identifies the ioctl calls to cloudfs.
 */
#define CLOUDFS_IOCTL_MAGIC 'C'

#define CLOUDFS_SNAPSHOT  (int)_IOR(CLOUDFS_IOCTL_MAGIC, 0, unsigned long *)
#define CLOUDFS_RESTORE (int)_IOW(CLOUDFS_IOCTL_MAGIC, 1, unsigned long *)
#define CLOUDFS_DELETE (int)_IOW(CLOUDFS_IOCTL_MAGIC, 2, unsigned long *)
#define CLOUDFS_SNAPSHOT_LIST  (int)_IOR(CLOUDFS_IOCTL_MAGIC, 3, unsigned long[CLOUDFS_MAX_NUM_SNAPSHOTS])
#define CLOUDFS_INSTALL_SNAPSHOT (int)_IOW(CLOUDFS_IOCTL_MAGIC, 4, unsigned long *)
#define CLOUDFS_UNINSTALL_SNAPSHOT (int)_IOW(CLOUDFS_IOCTL_MAGIC, 5, unsigned long *)
#endif
