#!/bin/sh

killall trayer

exec trayer --edge top --align right --SetDockType true --expand true --width 10 --alpha 0 --tint 0x002b36 --height 21 --transparent true
