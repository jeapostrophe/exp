#!/bin/sh

while true ; do
    pkill batterymon
    pkill -9 batterymon
    batterymon -t 16x16
done
