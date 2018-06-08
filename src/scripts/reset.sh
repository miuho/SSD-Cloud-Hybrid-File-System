#!/bin/bash

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source $SCRIPTS_DIR/paths.sh

pkill -9 cloudfs
$SCRIPTS_DIR/kill_server.sh
$SCRIPTS_DIR/cloudfs_controller.sh u
$SCRIPTS_DIR/format_disks.sh
rm -r $S3_DIR
rm -r $FUSE_MNT
rm -r $SSD_MNT
mkdir -p $S3_DIR
mkdir -p $FUSE_MNT
mkdir -p $SSD_MNT

echo "Cleaned up everything to its default state."
