#!/bin/sh

if (mpc | grep paused) &> /dev/null ; then
 COLOR="#dc322f"
else
 COLOR="#268bd2"
fi

echo -n "<fc=${COLOR}>"
echo -n $(mpc current | fold -w 20 | head -1)...
echo "</fc>"
