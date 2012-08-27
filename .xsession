#!/bin/zsh
. ~/.zshrc
cd ~

/usr/lib/notification-daemon-1.0/notification-daemon &

batterymon -t 16x16 &

syndaemon -t -k -i 2 -d &

xrdb -merge ~/.Xresources

xsetroot -solid '#fdf6e3'

start-trayer.sh 0 &

color-correct.sh
workrave &

~/.dropbox-dist/dropboxd &

#~/Dev/dist/qjoypad-4.1.0/local/bin/qjoypad &

urxvtd &

ibus-daemon --xim &

screen -UdmS lightning &

emacs &

conkeror &

pidgin &

miro &

#xmessage "Jay, reset the power settings" &

nvidia-settings -a InitialPixmapPlacement=2

exec xmonad
