source ~/.zshrc-dirs

setopt inc_append_history
setopt share_history
setopt auto_cd
setopt printeightbit

setopt autopushd pushdminus pushdsilent pushdtohome

autoload -U zmv
bindkey -e

#(tput cup 9999 0)
TPUT_END="" 
PROMPT_SYMB=❯
PROMPT_SYMB=⌁
PROMPT_SYMB=►
PROMPT_SYMB=⫸
# Hamburger
PROMPT_SYMB="🍔 "
# Pizza
PROMPT_SYMB="🍕 "
# Space Invader
PROMPT_SYMB="👾 "
# Poop
PROMPT_SYMB="💩 "

PROMPT_SYMB=⫸
PS1="${TPUT_END}%(?.%F{green}.%F{red})${PROMPT_SYMB}%f "

if [[ "$TERM" =~ "xterm" ]] ; then
    PS1="%S%~%s
$PS1"
fi
export PS1
TPS1="%~ ${PROMPT_SYMB}"
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

# OPAM configuration
. ~/.opam/opam-init/init.zsh > /dev/null 2> /dev/null || true
