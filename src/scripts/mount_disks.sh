#!/bin/bash

## Script to mount the SSD in the VirtualBox machine
##

SCRIPTS_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
source $SCRIPTS_DIR/paths.sh

mkdir -p $SSD_MNT
mount | grep "$SSD_MNT" &> /dev/null
before=$?

sudo mount.ssd $SSD_DEV $SSD_MNT &> /dev/null

mount | grep "$SSD_MNT" &> /dev/null
after=$?

if [ $before -eq $after ]; 
then
  echo "Mounting failed. Maybe it is already mounted?"
  exit 1
fi

echo "Mounting successful!"
