#!/bin/sh

for i in brcmsmac rfkill mac80211 cfg80211 ; do
    sudo modprobe -r ${i}
done

for i in brcmsmac rfkill cfg80211 mac80211 ; do
    sudo modprobe ${i}
done
