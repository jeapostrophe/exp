#!/bin/sh

pulseaudio --kill
killall pulseaudio
killall -9 pulseaudio
ls -l ~/.pulse* ; rm -fr ~/.pulse*
ls -l /tmp/pulse* ; rm -fr /tmp/pulse*
