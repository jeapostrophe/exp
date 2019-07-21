#!/bin/sh
exec avrdude -p atmega32u4 -c avr109 -U flash:w:atreus_jaytreus.hex -P /dev/cu.usbmodem1411
