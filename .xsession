#!/bin/zsh
. ~/.zshrc
cd ~

xrdb -merge ~/.Xresources

xsetroot -solid white

gnome-settings-daemon &

start-trayer.sh &

nm-applet &

/usr/bin/xcalib /etc/xcalib/profile.icc

workrave &

~/.dropbox-dist/dropboxd &

urxvtd &

ibus-daemon --xim &

# XXX Do I need to run bluetooth and sound?

screen -UdmS lightning &

emacs &

conkeror &

exec ~/.cabal/bin/xmonad
