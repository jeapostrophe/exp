#!/bin/sh

DMENU=~/Dev/dist/dmenu
export PATH=$DMENU:$PATH

dmenu_run -fn 'xft:unifont-12' -p '>' -i -nb "black" -nf "white" -sf "#cd8b00" -sb "black"
