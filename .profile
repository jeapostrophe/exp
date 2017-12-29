eval `/usr/libexec/path_helper -s`

export PATH=/opt/local/bin:/opt/local/sbin:$PATH
export PATH=/usr/local/Cellar/emacs/24.5/bin:$PATH
export PATH=/opt/local/libexec/perl5.16:$PATH
export PATH=/usr/local/bin:$PATH
export PATH=/Users/jay/Library/Python/2.7/bin:$PATH
export PATH=/Users/jay/Library/Python/3.6/bin:$PATH
export PATH=/Users/jay/.gem/ruby/2.0.0/bin:$PATH

export PYTHON_PATH=/Users/jay/Library/Python/2.7/site-packages:/Library/Python/2.7/site-packages

#export DYLD_FALLBACK_LIBRARY_PATH=/opt/local/lib/:$DYLD_FALLBACK_LIBRARY_PATH

export SVNROOT=$HOME/Dev/scm
export PROJS=$SVNROOT/github.jeapostrophe/work
export PLTHOME=$SVNROOT/plt
export PATH=$PLTHOME/racket/bin:$PATH
export DIST=$HOME/Dev/dist
export COQ_ROOT=$DIST/coq/local
export PATH=$COQ_ROOT/bin:$PATH
export CVS_RSH=ssh
export OCAMLRUNPARAM=b
export EDITOR=nvim
export TEXINPUTS=$PROJS/papers/etc:$PLTHOME/pkgs/slatex:$TEXINPUTS
export BIBINPUTS=$PROJS/papers/etc:$TEXINPUTS
export BSTINPUTS=$PROJS/papers/etc:$TEXINPUTS

#. /etc/locale.conf
export GTK_IM_MODULE=ibus
export XMODIFIERS=@im=ibus
export QT_IM_MODULE=ibus

alias ls='ls -G'
alias r='racket -il xrepl'
alias oew=emacsclient
alias oe='emacsclient -nc'
alias foe='fzf | xargs emacsclient -nc'
alias opene=oe
alias o=open
alias rd="raco docs"
alias git=hub
alias vim=nvim
alias vi=nvim

function rcd() { cd $(raco fc $*) }

export EMACS_SERVER_PORT=50000
export EMACS_SERVER_FILE=~/.emacs.d/server/lightning

export FZF_DEFAULT_OPTS="--cycle --algo=v1 --color=light"

export GPG_TTY=$(tty)

export PATH="$HOME/.cargo/bin:$PATH"
