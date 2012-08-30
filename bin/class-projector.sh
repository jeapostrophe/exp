#!/bin/bash

# https://wiki.archlinux.org/index.php/Xrandr

#xrandr --output DP-1 --newmode "800x600_59.90"   38.00  800 832 912 1024  600 603 607 624 -hsync +vsync

MODES=("1440 900 60" "1280 1024 50" "1280 1024 59.9" "1280 1024 60" "800 600 60" "800 600 59.9" "800 600 50")
OUTPUTS=("DP-1" "DP-2")

for mode in "${MODES[@]}" ; do
    echo $mode
    xrandr --rmmode "${mode}"
    MODELINE=$(gtf $mode | tail -2 | head -1 | cut -f "5-" -d " ")
    xrandr --newmode "${mode}" ${MODELINE}

    for disp in "${OUTPUTS[@]}" ; do
        sudo xrandr --delmode "${disp}" "${mode}"
        sudo xrandr --addmode "${disp}" "${mode}"
    done
done

exit 1

for i in DP-1 DP-2 ; do
    for j in "1280x1024_59.90" "1280x1024_60.00" "800x600_60.00" "800x600_59.90" ; do
        xrandr --delmode ${i} ${j}
    done
    for j in "1280x1024_59.90" "1280x1024_60.00" "800x600_60.00" "800x600_59.90" ; do
        xrandr --addmode ${i} ${j}
    done
done

# https://kis.kellogg.northwestern.edu/Pages/ExternalDisplaysLinux.aspx

# xrandr --output DP-2 --auto --output DP-1 --auto --same-as DP-2

xrandr --output DP-2 --mode "1280x1024_60.00" --output DP-1 --mode "1280x1024_59.90" --same-as DP-2
