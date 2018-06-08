#!/bin/bash

## Script to unmount the SSD in the VirtualBox machine
##

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source $SCRIPTS_DIR/paths.sh

mount | grep "$SSD_MNT" &> /dev/null
before=$?

sudo umount.ssd $SSD_DEV &> /dev/null

mount | grep "$SSD_MNT" &> /dev/null
after=$?

if [ $before -eq $after ]; 
then
  echo "Unmounting failed. Maybe it is not mounted?"
  exit 1
fi

echo "Unmounting successful!"
