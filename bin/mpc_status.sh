#!/usr/bin/sh

if [ "${1}" != "" ] ; then
    mpc ${1}
fi

if (mpc | grep paused) &> /dev/null ; then
 COLOR="#dc322f"
else
 COLOR="#268bd2"
fi

CUR=$(mpc -f '%artist%, %album%-%track%' current)

PIPE=~jay/.mpc-pipe
if [ ! -e ${PIPE} ] ; then
    mkfifo ${PIPE}
fi
echo "<fc=${COLOR}>${CUR}</fc>" > ${PIPE}
