#!/bin/sh

FILE=$1
HOST=${2:-vassar}

rsync -h --progress -a ${FILE} ${HOST}:public_html/video/${FILE}
