#!/bin/sh

killall trayer

exec ~/Dev/dist/trayer-srg/trayer --edge top --align right --SetDockType true --expand true --width 5 --alpha 0 --tint 0x002b36 --height 19 --transparent true --monitor $*
