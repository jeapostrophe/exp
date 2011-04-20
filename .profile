export PATH=/opt/local/bin:/opt/local:/sbin:/Developer/usr/bin:$PATH
export MANPATH=/opt/local/share/man:$MANPATH
export TEXINPUTS=/opt/local/share/coq/latex:$TEXINPUTS
#export DYLD_LIBRARY_PATH=$DYLD_LIBRARY_PATH:/opt/local/lib:/Developer/usr/lib:
#export DYLD_FRAMEWORK_PATH=$DYLD_FRAMEWORK_PATH:/opt/local/Library/Frameworks:

export SVNROOT=$HOME/Dev/scm
export PROJS=$SVNROOT/github.jeapostrophe/work
export PLTHOME=$SVNROOT/plt
export PATH=$PLTHOME/bin:$PATH
export DIST=$HOME/Dev/dist
export COQ_ROOT=$DIST/coq/local
export PATH=$COQ_ROOT/bin:$PATH
export CVS_RSH=ssh
export OCAMLRUNPARAM=b
export EDITOR=vim
export TEXINPUTS=$PROJS/papers/etc:$PLTHOME/collects/slatex:$TEXINPUTS
export BIBINPUTS=$PROJS/papers/etc:$TEXINPUTS
export BSTINPUTS=$PROJS/papers/etc:$TEXINPUTS

alias opene='open -a ~/Applications/Aquamacs.app'

function teamtmp() {
    NAME=$(date +%Y%m%d%H%M-)$(basename $1)
    scp -r $1 schizo.cs.byu.edu:public_html/tmp/${NAME}
    echo http://faculty.cs.byu.edu/~jay/tmp/${NAME}
}

function findss() {
    find . -name '*.ss' -o -name '*.scm' -o -name '*.rkt' -o -name '*.scrbl' | xargs grep -e $*
}

function sto() {
    touch $*
    git add $*
    open $*
}	

function stoe() {
    touch $*
    git add $*
    opene $*
}	

##
# Your previous /Users/jay/.profile file was backed up as /Users/jay/.profile.macports-saved_2009-09-09_at_10:16:30
##

# MacPorts Installer addition on 2009-09-09_at_10:16:30: adding an appropriate PATH variable for use with MacPorts.
export PATH=/opt/local/bin:/opt/local/sbin:$PATH
# Finished adapting your PATH environment variable for use with MacPorts.

export LC_CTYPE=ja_JP.UTF-8
