#!/bin/sh

xrandr --newmode "1280x1024_59.90"  108.70  1280 1360 1496 1712  1024 1025 1028 1060  -HSync +Vsync
xrandr --newmode "1280x1024_60.00"  108.88  1280 1360 1496 1712  1024 1025 1028 1060  -HSync +Vsync
xrandr --newmode "800x600_60.00"  38.22  800 832 912 1024  600 601 604 622  -HSync +Vsync
xrandr --newmode "800x600_59.90"  38.09  800 832 912 1024  600 601 604 621  -HSync +Vsync

for i in DP-1 DP-2 ; do
    for j in "1280x1024_59.90" "1280x1024_60.00" "800x600_60.00" "800x600_59.90" ; do
        xrandr --addmode ${i} ${j}
    done
done
