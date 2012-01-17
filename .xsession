#!/bin/zsh
. ~/.zshrc
cd ~

xrdb -merge ~/.Xresources

xsetroot -solid white

gnome-settings-daemon &

start-trayer.sh &

color-correct.sh

nm-applet &

workrave &

~/.dropbox-dist/dropboxd &

urxvtd &

ibus-daemon --xim &

# XXX Do I need to run bluetooth and sound?

screen -UdmS lightning &

emacs &

conkeror &

exec ~/.cabal/bin/xmonad
