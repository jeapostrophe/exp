#!/bin/bash

nvidia-settings -q CurrentMetaMode

# Did I need to run disper-e first?

if [ "x$1" = "xon" ] ; then
	#nvidia-settings --assign CurrentMetaMode="DFP-2: 1440x900 { ViewPortIn=1400x900, ViewPortOut=1400x900+20+0 }, DFP-1: 1400x1050 { ViewPortIn=1400x900, ViewPortOut=1400x900+0+75 }"
	nvidia-settings --assign CurrentMetaMode="DFP-2: 1440x900 { ViewPortIn=640x480, ViewPortOut=640x480+0+0 }, DFP-1: 640x480 { ViewPortIn=640x480, ViewPortOut=640x480+0+0 }"
else 
	nvidia-settings --assign CurrentMetaMode="DPY-2: 1440x900 @1440x900"
fi

nvidia-settings -q CurrentMetaMode

~/bin/start-trayer.sh 0 &
