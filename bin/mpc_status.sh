#!/bin/sh

if (mpc | grep paused) &> /dev/null ; then
 COLOR="#dc322f"
else
 COLOR="#268bd2"
fi

echo -n "<fc=${COLOR}>"
echo -n $(mpc current | perl -ne 's/^(.{19}).*(.{19})$/\1...\2/; print')
echo "</fc>"
