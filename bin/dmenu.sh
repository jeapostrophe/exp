#!/bin/sh

DMENU=~/Dev/dist/dmenu
export PATH=$DMENU:$PATH

dmenu_run -fn 'xft:unifont-12' -p '>' -i -nb "black" -nf "grey" -sb "#cd8b00" -sf "white"
