#!/bin/sh
export LANG=ja_JP.utf8
export LANGUAGE=$LANG
export LC_ALL=$LANG
export LC_TIME=$LANG
export LC_CTYPE=$LANG
exec date +"%a%b%e %H:%M"
