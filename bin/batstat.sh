#!/bin/sh

source ~/bin/solarized.sh

CHARGING=1
if acpi -b | grep Discharging &>/dev/null ; then
    CHARGING=0
fi

PERCENT_S=$(acpi -b | awk -F, '{print $2}')
PERCENT_N=$(echo $PERCENT_S | awk -F% '{print $1}')

if acpi -b | grep Unknown &> /dev/null ; then
    TIME="??:??"
else
    TIME=$(acpi -b | perl -ne 's/^.+(..:..):...+$/\1/; print;')
fi

COLOR=$GREEN
if (($PERCENT_N <= 95)) ; then
    COLOR=$CYAN
fi
if (($PERCENT_N <= 75)) ; then
    COLOR=$BLUE
fi
if (($PERCENT_N <= 50)) ; then
    COLOR=$VIOLET
fi
if (($PERCENT_N <= 30)) ; then
    COLOR=$MAGENTA
fi
if (($PERCENT_N <= 15)) ; then
    COLOR=$RED
fi
if (($PERCENT_N <= 10)) ; then
    COLOR=$ORANGE
fi
if (($PERCENT_N <= 05)) ; then
    COLOR=$YELLOW
fi

echo -n "<fc=$COLOR>"
echo -n "$PERCENT_S"
echo -n "</fc>"

echo -n " "

if (($CHARGING == 1)) ; then
    echo -n "<fc=$BLUE>"
else
    echo -n "<fc=$RED>"
fi
echo -n "$TIME"
echo "</fc>"
