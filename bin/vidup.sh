#!/bin/sh

FILE=$1
HOST=${2:-bacteria}

scp ${FILE} ${HOST}:public_html/video/
