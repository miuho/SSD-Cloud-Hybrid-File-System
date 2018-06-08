#!/bin/bash

##
## Script to start the CloudFS file system
##

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source $SCRIPTS_DIR/paths.sh

if [ "$1" = "m" ]
then
    mkdir -p ${FUSE_MNT}
    shift             # discard the first arg
    $SCRIPTS_DIR/mount_disks.sh
    $CLOUDFS_BIN "$@"
elif [ "$1" = "u" ]
then
    sync
    fusermount -u ${FUSE_MNT}
    if [ $? -ne 0 ]; then
        echo "Trying to do a lazy unmount for cloudfs"
        fusermount -u -z ${FUSE_MNT}
    fi
    $SCRIPTS_DIR/umount_disks.sh
elif [ "$1" = "x" ]
then
    sync
    fusermount -u ${FUSE_MNT}
    if [ $? -ne 0 ]; then
        echo "Trying to do a lazy unmount for cloudfs"
        fusermount -u -z ${FUSE_MNT}
    fi

    $SCRIPTS_DIR/umount_disks.sh  
    $SCRIPTS_DIR/mount_disks.sh  
    shift             # discard the first arg
    ${CLOUDFS_BIN} "$@"
else
    echo "***ERROR"
    echo "Usage: ./scriptName <MODE>"
    echo ""
    echo "where, MODE is one of the following ..."
    echo "m for mount, u for unmount, x for (unmount+mount) to drop caches"
fi
