export PATH=$HOME/.cabal/bin:$PATH

export SVNROOT=$HOME/Dev/scm
export PROJS=$SVNROOT/github.jeapostrophe/work
export PLTHOME=$SVNROOT/plt
export PATH=$PLTHOME/racket/bin:$PATH
export DIST=$HOME/Dev/dist
export COQ_ROOT=$DIST/coq/local
export PATH=$COQ_ROOT/bin:$PATH
export CVS_RSH=ssh
export OCAMLRUNPARAM=b
export EDITOR='emacsclient -c'
export TEXINPUTS=$PROJS/papers/etc:$PLTHOME/pkgs/slatex:$TEXINPUTS
export BIBINPUTS=$PROJS/papers/etc:$TEXINPUTS
export BSTINPUTS=$PROJS/papers/etc:$TEXINPUTS

. /etc/locale.conf
export GTK_IM_MODULE=ibus
export XMODIFIERS=@im=ibus
export QT_IM_MODULE=ibus

alias ls='ls --color=auto'
alias r='racket -il xrepl'
alias oew=emacsclient
alias oe='emacsclient -nc'
alias opene=oe
alias o=open

export EMACS_SERVER_PORT=50000
export EMACS_SERVER_FILE=~/.emacs.d/server/lightning
