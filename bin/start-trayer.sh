#!/bin/sh

killall trayer

/usr/bin/xcalib /etc/xcalib/profile.icc

exec trayer --edge top --align right --SetDockType true --expand true --width 10 --alpha 0 --tint 0x000000 --height 17 --transparent true
