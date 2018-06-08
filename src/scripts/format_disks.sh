#!/bin/bash

## Script to create the Ext4 file system on two different disks
##

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source $SCRIPTS_DIR/paths.sh

echo "*** Formatting SSD device $SSD_DEV with ext4 ..."
echo "***"
sudo format.ssd $SSD_DEV
