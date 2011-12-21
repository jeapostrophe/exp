export PATH=$HOME/.cabal/bin:$PATH

export SVNROOT=$HOME/Dev/scm
export PROJS=$SVNROOT/github.jeapostrophe/work
export PLTHOME=$SVNROOT/plt
export PATH=$PLTHOME/bin:$PATH
export DIST=$HOME/Dev/dist
export COQ_ROOT=$DIST/coq/local
export PATH=$COQ_ROOT/bin:$PATH
export CVS_RSH=ssh
export OCAMLRUNPARAM=b
export EDITOR='emacsclient -nc'
export TEXINPUTS=$PROJS/papers/etc:$PLTHOME/collects/slatex:$TEXINPUTS
export BIBINPUTS=$PROJS/papers/etc:$TEXINPUTS
export BSTINPUTS=$PROJS/papers/etc:$TEXINPUTS

export LANG=C

alias r='racket -il xrepl'
alias oew=emacsclient
alias oe='emacsclient -nc'
alias opene=oe
alias o=open

#function oes() {
#    for i in $* ; do
#        oe $i
#    done
#}

export EMACS_SERVER_PORT=50000
export EMACS_SERVER_FILE=~/.emacs.d/server/lightning

#function teamtmp() {
#    NAME=$(date +%Y%m%d%H%M-)$(basename $1)
#    scp -r $1 weapons.cs.byu.edu:public_html/tmp/${NAME}
#    echo http://faculty.cs.byu.edu/~jay/tmp/${NAME}
#}

#function findss() {
#    find . -name '*.ss' -o -name '*.scm' -o -name '*.rkt' -o -name '*.scrbl' | xargs grep -e $*
#}

#function sto() {
#    mkdir -p $(dirname $1)
#    touch $*
#    git add $*
#    o $*
#}	

#function stoe() {
#    mkdir -p $(dirname $1)
#    touch $*
#    git add $*
#    oe $*
#}	

