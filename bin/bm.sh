#!/bin/sh

while sleep 1 ; do
    pkill batterymon
    pkill -9 batterymon
    echo restarting
    batterymon -t 16x16
    if [ $? = 139 ] ; then
	exit 1
    fi
done
