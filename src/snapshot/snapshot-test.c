/** 
 * @file snapshot_test.c
 * @brief This file calls the snpashots ioctls implemented by 
 * cloudfs.
 * @author rohanseh
 * @date 2015-03-22
 */

#include <sys/types.h>
#include <sys/fcntl.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "../snapshot/snapshot-api.h"

int main(int argc, char **argv)
{
    unsigned long timestamp;
    unsigned long timestamp_list[CLOUDFS_MAX_NUM_SNAPSHOTS + 1] = {0};

    char cmd;
    int fd;

    if (argc < 3)
        goto usage;

    fd = open(argv[1], O_RDONLY);
    if (fd < 0) 
    {
        perror(argv[1]);
        return 1;
    }

    char* arg_ts = argv[3];
    cmd = tolower(argv[2][0]);

    switch (cmd) 
    {
        case 's':
            if (ioctl(fd, CLOUDFS_SNAPSHOT, &timestamp)) 
            {
                perror("ioctl");
                return 1;
            }
            printf("%lu", timestamp);
            return 0;
        case 'r':
            timestamp = strtoul(arg_ts, NULL, 10);
            printf("Restoring %s %lu\n", arg_ts, timestamp);
            if (ioctl(fd, CLOUDFS_RESTORE, &timestamp)) 
            {
                perror("ioctl");
                return 1;
            }
            return 0;
        case 'l':
            if (ioctl(fd, CLOUDFS_SNAPSHOT_LIST, timestamp_list)) 
            {
                perror("ioctl");
                return 1;
            }
            unsigned long* current_ts = timestamp_list;
            int i = 0;
            while (i < CLOUDFS_MAX_NUM_SNAPSHOTS && *current_ts != 0)
            {
                printf("Snapshot %lu\n", *current_ts);
                i++;
                current_ts++;
            }
            return 0;
        case 'd':
            timestamp = strtoul(arg_ts, NULL, 10);
            printf("Deleting %s %lu\n", arg_ts, timestamp);
            if (ioctl(fd, CLOUDFS_DELETE, &timestamp)) 
            {
                perror("ioctl");
                return 1;
            }
            return 0;
        case 'i':
            timestamp = strtoul(arg_ts, NULL, 10);
            printf("Installing %s %lu\n", arg_ts, timestamp);
            if (ioctl(fd, CLOUDFS_INSTALL_SNAPSHOT, &timestamp)) 
            {
                perror("ioctl");
                return 1;
            }
            return 0;
        case 'u':
            timestamp = strtoul(arg_ts, NULL, 10);
            printf("Uninstalling %s %lu\n", arg_ts, timestamp);
            if (ioctl(fd, CLOUDFS_UNINSTALL_SNAPSHOT, &timestamp)) 
            {
                perror("ioctl");
                return 1;
            }
            return 0;
    }

usage:
    fprintf(stderr, "./snapshot <path_to_fuse>/.snapshot s|r|l|i|u\n");
    return 1;
}
