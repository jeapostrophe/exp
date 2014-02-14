#!/bin/zsh
. ~/.zshrc
cd ~

/usr/lib/notification-daemon-1.0/notification-daemon &

xrdb -merge ~/.Xresources

xsetroot -solid '#fdf6e3'

disp m & 

workrave &

urxvtd &

ibus-daemon --xim &

start-pulseaudio-x11 &

synclient PalmDetect=1 TapButton1=0 TapButton2=0 TapButton3=0 MaxTapMove=0 MaxTapTime=0
syndaemon -t -k -i 2 -d &

minidlnad -f ~/.config/minidlna.conf -P /tmp/minidlna.pid

if (screen -list | grep lightning) ; then
	echo Screen exists
else
	screen -UdmS lightning &
fi

if [ "$1" = "default" ] ; then
    mpd ~/.mpdconf &

	emacs &

	conkeror &

	pidgin &

	miro &

	google-chrome-stable &
fi

exec xmonad
