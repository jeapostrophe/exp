#!/bin/bash

tmux=/usr/local/bin/tmux

for i in $($tmux list-sessions | grep -v attached | awk -F: '{print $1}') ; do
    $tmux kill-session -t $i
done

exec $tmux new-session -t 0
