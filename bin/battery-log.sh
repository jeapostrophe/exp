#!/bin/sh
(echo -n "$(date +%s) " ; acpi -i | tail -1) >> ~/Documents/battery.log
