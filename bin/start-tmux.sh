#!/bin/bash

# This script takes a session name as its argument, using "default" if not
# given, and launches a terminal with a tmux session by that name or a
# derived name.  There are four cases:
#
# 1) The named session does not exist:
#    --> create it.
# 2) The named session exists, but is not attached to any clients:
#    --> attach to it.
# 3) The named session exists, and is attached to a client:
#    --> derive a new name by appending a number, incrementing that number
#        until we find a session name with no clients attached. Then:
#
#        a) The resulting name is an existing session:
#           --> attach to it.
#        b) Otherwise:
#           --> create it as a linked session.

session=${1-default}
sessions=($(tmux ls | cut -d: -f1 2>/dev/null))
clients=($(tmux lsc | awk '{print $2}' 2>/dev/null))

function session-exists {
    for i in "${sessions[@]}"; do
        if [ "$i" = "$1" ]; then
            return 0
        fi
    done
    return 1
}

function client-exists-for {
    for i in "${clients[@]}"; do
        if [ "$i" = "$1" ]; then
            return 0
        fi
    done
    return 1
}

if session-exists "$session"; then
    if client-exists-for "$session"; then
        n=1
        while session-exists "$session$n" && client-exists-for "$session$n"; do
            let n=n+1
        done
        if session-exists "$session$n"; then
            exec tmux attach -t "$session$n"
        else
            exec tmux new -s "$session$n" -t "$session"
        fi
    else
        exec tmux attach -t "$session"
    fi
else
    exec tmux new -s "$session"
fi
