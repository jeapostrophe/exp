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

#~/Dev/dist/qjoypad-4.1.0/local/bin/qjoypad &

urxvtd &

ibus-daemon --xim &

# XXX Do I need to run bluetooth and sound?

#screen -UdmS lightning &

emacs &

conkeror &

#start-skype.sh &

exec ~/.cabal/bin/xmonad
