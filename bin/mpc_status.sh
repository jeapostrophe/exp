#!/bin/sh

if (mpc | grep paused) &> /dev/null ; then
 COLOR="#dc322f"
else
 COLOR="#268bd2"
fi

echo -n "<fc=${COLOR}>"
echo -n $(mpc -f '%artist%, %album%-%track%' current)
echo "</fc>"
