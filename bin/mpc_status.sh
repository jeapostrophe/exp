#!/bin/sh

if (mpc | grep paused) &> /dev/null ; then
 COLOR="#dc322f"
else
 COLOR="#268bd2"
fi

echo -n "<fc=${COLOR}>"
echo -n $(mpc current | perl -ne 's/^(.{18}).*(.{18})$/\1...\2/; print')
echo "</fc>"
