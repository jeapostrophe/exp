#!/bin/sh
eval $(/usr/libexec/path_helper -s)

export PATH=/usr/local/bin:$PATH
export PATH=/usr/local/sbin:$PATH
export PATH=$HOME/Library/Python/2.7/bin:$PATH
export PATH=$HOME/Library/Python/3.6/bin:$PATH
export PATH=$HOME/Library/Python/3.7/bin:$PATH
export PATH=$HOME/.gem/ruby/2.0.0/bin:$PATH
export PATH=$HOME/.cargo/bin:$PATH
export PATH=$HOME/go/bin:$PATH
. ~/.opam/opam-init/variables.sh > /dev/null 2> /dev/null || true
export PATH=/Applications/kitty.app/Contents/MacOS/:$PATH
export PATH=$HOME/Dev/scm/plt/racket/bin:$PATH
export PATH=$HOME/.jwm/bin:$PATH
export PATH=$HOME/bin:$PATH
export PATH=$HOME/sbin:$PATH
export PATH=$HOME/.local/bin:$PATH

export PYTHON_PATH=$HOME/Library/Python/2.7/site-packages:/Library/Python/2.7/site-packages

export CVS_RSH=ssh

if [ -n "${NVIM_LISTEN_ADDRESS+x}" ]; then
  export EDITOR='nvr'
else
  export EDITOR=nvim
fi

export BROWSER=open

export CLICOLOR=1

alias git=hub
alias vim=$EDITOR
alias vi=$EDITOR
alias ed=$EDITOR
alias cat=bat

alias e=$EDITOR
alias tw=timew
alias tws=timew-startfzf
alias twt="timew stop"
alias w="w3m ~/sbin/start-page/index.html"
alias now="date +%s"

rcd() {
  cd $(racket -l find-collection/run -- $@)
}

export EMACS_SERVER_PORT=50000
export EMACS_SERVER_FILE=$HOME/.emacs.d/server/lightning

export FZF_DEFAULT_COMMAND='fd --follow --type file --color=never'
export FZF_CTRL_T_COMMAND="$FZF_DEFAULT_COMMAND"
export FZF_DEFAULT_OPTS="--ansi --cycle --algo=v1 --color=light --layout=reverse-list --prompt='⫸ '"

export TMPDIR=/tmp/

export GPG_TTY=$(tty)

export PASSWORD_STORE_ENABLE_EXTENSIONS=true

export TZ="America/New_York"

export RIPGREP_CONFIG_PATH=$HOME/.ripgreprc
