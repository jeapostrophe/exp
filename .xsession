#!/bin/zsh
. ~/.zshrc
cd

xrdb -merge ~/.Xresources

xsetroot -solid white

gnome-settings-daemon &

trayer --edge top --align right --SetDockType true --expand true --width 10 --alpha 0 --tint 0x000000 --height 17 --transparent true &

nm-applet &

/usr/bin/xcalib /etc/xcalib/profile.icc

workrave &

~/.dropbox-dist/dropboxd &

urxvtd &

ibus-daemon --xim &

# XXX Do I need to run bluetooth and sound?

if ! screen -S lightning -list | grep "No Sockets" ; then
    screen -UdmS lightning &
fi

emacs &

conkeror &

exec ~/.cabal/bin/xmonad
