#!/usr/bin/sh

source ~/bin/solarized.sh

if [ "x$1" == "xtest" ] ; then
    CHARGING=0
    PERCENT_S="3%"
    TIME="0:09"
else
    CHARGING=1
    if acpi -b | grep Discharging &>/dev/null ; then
        CHARGING=0
    fi

    PERCENT_S=$(acpi -b | awk -F, '{print $2}')

    if acpi -b | grep Unknown &> /dev/null ; then
        TIME="??:??"
    elif acpi -b | grep Full &> /dev/null ; then
        TIME="     "
    elif acpi -b | grep "zero rate" &> /dev/null ; then
        TIME="     "
    else
        TIME=$(acpi -b | perl -ne 's/^.+(..:..):...+$/\1/; print;')
    fi
fi

PERCENT_N=$(echo $PERCENT_S | awk -F% '{print $1}')

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

function espeakwav() {
    if ! [ -f "$2" ] ; then
        espeak -a 200 -k20 -z "$1" -w "$2"
    fi
    mplayer "$2" &>/dev/null &
}

if (($CHARGING == 1)) ; then
    echo -n
else
    if (($PERCENT_N <= 02)) ; then
        sudo systemctl hibernate
    elif (($PERCENT_N <= 03)) ; then
        espeakwav "Hibernation Eminent" /tmp/he.wav
    elif (($PERCENT_N <= 05)) ; then
        espeakwav "Warning Battery Extremely Low" /tmp/wbel.wav
    elif (($PERCENT_N <= 10)) ; then
        espeakwav "Warning Battery Low" /tmp/wbl.wav
    fi
fi
