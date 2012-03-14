#!/bin/sh

DMENU=~/Dev/dist/dmenu
export PATH=$DMENU:$PATH

dmenu_run -fn "xft:Bitstream Vera Sans Mono:pixelsize=13:scalable=true:antialias=true" -p '>' -i -nb "black" -nf "white" -sf "#cd8b00" -sb "black"
