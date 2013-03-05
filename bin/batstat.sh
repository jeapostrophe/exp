#!/bin/sh

#                       Run BatteryP ["BAT0"]
#                          ["-t", "<acstatus><left>% <timeleft></fc>",
#                           "--",
#                           "-O", "<fc=#859900>",
#                           "-o", "<fc=#dc322f>",
#                           "-f", "ADP1/online" ]
#                          600,

AC=1
if acpi -a | grep off-line &>/dev/null ; then
 AC=0
fi

CHARGING=1
if acpi -b | grep Discharging &>/dev/null ; then
 CHARGING=0
fi

PERCENT_S=$(acpi -b | awk -F, '{print $2}')
PERCENT_N=$(echo $PERCENT_S | awk -F% '{print $1}')

TIME=$(acpi -b | perl -ne 's/^.+(..:..):...+$/\1/; print;')

echo $AC $CHARGING $PERCENT_S $PERCENT_N $TIME
