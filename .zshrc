source ~/.profile

setopt inc_append_history
setopt share_history
setopt auto_cd
setopt printeightbit

hash -d scm=$SVNROOT
hash -d plt=$PLTHOME
hash -d pkgs=~plt/pkgs
hash -d epkgs=~plt/extra-pkgs
hash -d ws=~epkgs/web-server
hash -d drdr=~epkgs/drdr
hash -d pkgi=~epkgs/pkg-index
hash -d work=$PROJS
hash -d papers=~work/papers
hash -d planet=~scm/github.jeapostrophe.planet
hash -d github=~scm/github.jeapostrophe
hash -d home=~github/home
hash -d gb=~github/get-bonus
hash -d lll=~github/lll
hash -d exp=~scm/github.jeapostrophe/exp
hash -d fin=~scm/github.jeapostrophe/home/finance
hash -d j=~github/home/journal
hash -d blogs=~scm/blogs

hash -d courses=~work/courses
hash -d 301=~courses/2016/fall/301
hash -d 304=~courses/2016/fall/304
hash -d 305=~courses/2015/fall/305
hash -d 308=~courses/2016/spring/308
hash -d 404=~courses/2016/summer/404

hash -d utrs=~scm/bitbucket.jeapostrophe/consulting-utrs

export PATH=~exp/bin:~work/papers/etc/bin:$PATH

setopt autopushd pushdminus pushdsilent pushdtohome

autoload -U zmv
bindkey -e

export PS1="%S%~%s
%# "
TPS1="%~ %# "
RECENTFILES=8

JE_CUSTOM_NAME=0
function rename-pane {
    print -Pn "\e]0;$1\a\033k$1\033\\"
    JE_CUSTOM_NAME=1
}
function cancel-rename-pane {
    JE_CUSTOM_NAME=0
}

# Track directory, username, and cwd for remote logons.
if [[ "$TERM" =~ "screen" ]] ; then
    precmd () {
        if [ ${JE_CUSTOM_NAME} = '0' ] ; then
            print -Pn "\e]0;$TPS1\a\033k$TPS1\033\\"
        fi
    }
    preexec () {
        if [ ${JE_CUSTOM_NAME} = '0' ] ; then
            print -Pn "\e]0;$TPS1 $2\a\033k$TPS1 $2\033\\"
        fi
    }
fi

ZDIR=~/.zdir

# Read in ZDIR
write_zdir () {
    pwd >! $ZDIR
}

# Read in ZDIR
read_zdir () {
    pushd "$(cat $ZDIR)"
}

chpwd () {
    # Save what directory we are in for the future
    write_zdir
    # Show recently modified files
    ls -t | head -$RECENTFILES | tr '\n' '\0' | xargs -0 ls -Gd
}

if [ $(pwd) = ${HOME} ] ; then
    read_zdir
fi

# Completions
autoload -U compinit
compinit

if which compdef &>/dev/null ; then
    compdef -d git
    compdef -d svn
fi
compctl -g '*(/)' rmdir dircmp
compctl -g '*(-/)' cd chdir dirs pushd
#compctl -z -P '%' bg
#compctl -j -P '%' fg jobs disown
#compctl -j -P '%' + -s '`ps -x | tail +2 | cut -c1-5`' wait

# Caching
zstyle ':completion:*' use-cache on
zstyle ':completion:*' cache-path ~/.zsh/cache

# Adding known hosts
#local _myhosts
#if [[ -f "$HOME/.ssh/known_hosts" ]]; then
#  _myhosts=( ${${${${(f)"$(<$HOME/.ssh/known_hosts)"}:#[0-9]*}%%\ *}%%,*} )
#  zstyle ':completion:*' hosts $_myhosts
#fi

# Ignore what's in the line
#zstyle ':completion:*:(rm|kill|diff):*' ignore-line yes

function oes() {
    for i in $* ; do
        oe $i
    done
}

function teamtmp() {
    NAME=$(date +%Y%m%d%H%M-)$(basename $1)
    scp -r $1 uml:public_html/tmp/${NAME}
    echo http://www.cs.uml.edu/~jmccarth/tmp/${NAME}
}

function findss() {
    find . -name '*.ss' -o -name '*.scm' -o -name '*.rkt' -o -name '*.scrbl' | xargs grep -e $*
}

function sto() {
    mkdir -p $(dirname $1)
    touch $*
    git add $*
    o $*
}	

function stoe() {
    mkdir -p $(dirname $1)
    touch $*
    git add $*
    oe $*
}	

function racketdoclink() {
    rm -f ~/.racket/doc
    DEST=$(racket -e '(require setup/dirs) (displayln (path->string (find-user-doc-dir)))')
    ln -s $DEST ~/.racket/doc
}

function rfc() {
  cd `racket -l find-collection/run $1`
}
alias am=mathomatic
alias e="mathomatic -e --"

#racketdoclink

export REPORTTIME=10

[ -f ~/.fzf.zsh ] && source ~/.fzf.zsh
