#!/bin/bash

kill -15 `ps -lef | grep s3server.pyc | grep -v grep | awk '{print $4}'` > /dev/null 2>&1
