#!/bin/zsh
. ~/.zshrc
cd ~

/usr/lib/notification-daemon-1.0/notification-daemon &

~/bin/bm.sh &

xrdb -merge ~/.Xresources

xsetroot -solid '#fdf6e3'

start-trayer.sh 0 &

workrave &

urxvtd &

ibus-daemon --xim &

start-pulseaudio-x11 &

if (screen -list | grep lightning) ; then
	echo Screen exists
else
	screen -UdmS lightning &
fi

if [ "$1" = "default" ] ; then
	emacs &

	conkeror &

	pidgin &

	miro &

	google-chrome &
fi

exec xmonad
