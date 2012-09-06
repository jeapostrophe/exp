#!/bin/bash

# First run "disper -e" to get the second one turned on

# Projector
# DFP-2: 1440x900 { ViewPortIn=1400x900, ViewPortOut=1400x900+20+0 }, DFP-1: 1400x1050 { ViewPortIn=1400x900, ViewPortOut=1400x900+0+75 }, DFP-0: NULL;

# Laptop
# DFP-2: 1440x900, DFP-1: NULL, DFP-0: NULL;

# Desktop
# DFP-2: NULL, DFP-1: NULL, DFP-0: 1920x1080;

nvidia-settings -q CurrentMetaMode

if [ "x$1" = "xon" ] ; then
    # This is what OS X can do
	#nvidia-settings --assign CurrentMetaMode="DFP-2: 1440x900 { ViewPortIn=1400x900, ViewPortOut=1400x900+20+0 }, DFP-1: 1400x1050 { ViewPortIn=1400x900, ViewPortOut=1400x900+0+75 }"

    # This one works and has a tiny box on the laptop and a very small resolution on the screen
	nvidia-settings --assign CurrentMetaMode="DFP-2: 1440x900 { ViewPortIn=640x480, ViewPortOut=640x480+400+210 }, DFP-1: 640x480 { ViewPortIn=640x480, ViewPortOut=640x480+0+0 }"

else 
	nvidia-settings --assign CurrentMetaMode="DPY-2: 1440x900 @1440x900"
fi

nvidia-settings -q CurrentMetaMode

~/bin/start-trayer.sh 0 &
