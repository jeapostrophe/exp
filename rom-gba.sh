#!/bin/bash

ROOT="/home/jay/Games/Nintendo - Game Boy Advance"
ROMS=${ROOT}/Roms
CARD=${ROOT}/Card

function open () {
    echo $*
}

mkdir "${CARD}"
while read line ; do
    unzip "${ROMS}/${line}" -d "${CARD}"
done < ~/list.txt
