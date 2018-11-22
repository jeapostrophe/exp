#!/bin/sh
eval $(/usr/libexec/path_helper -s)

export PATH=/usr/local/bin:$PATH
export PATH=$HOME/Library/Python/2.7/bin:$PATH
export PATH=$HOME/Library/Python/3.6/bin:$PATH
export PATH=$HOME/.gem/ruby/2.0.0/bin:$PATH
export PATH=$HOME/.cargo/bin:$PATH
. ~/.opam/opam-init/variables.sh > /dev/null 2> /dev/null || true
export PATH=$HOME/Dev/scm/plt/racket/bin:$PATH
export PATH=$HOME/bin:$PATH
export PATH=$HOME/sbin:$PATH

export PYTHON_PATH=$HOME/Library/Python/2.7/site-packages:/Library/Python/2.7/site-packages

export CVS_RSH=ssh
export EDITOR=kak

export CLICOLOR=1

alias git=hub
alias vim=$EDITOR
alias vi=$EDITOR
alias ed=$EDITOR

function rcd() { cd $(racket -l find-collection/run -- $@) }

export EMACS_SERVER_PORT=50000
export EMACS_SERVER_FILE=$HOME/.emacs.d/server/lightning

export FZF_DEFAULT_OPTS="--cycle --algo=v1 --color=light --layout=reverse-list --prompt='⫸ '"

export GPG_TTY=$(tty)
