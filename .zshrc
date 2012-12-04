source ~/.profile

setopt inc_append_history
setopt share_history
setopt auto_cd
setopt printeightbit

hash -d scm=$SVNROOT
hash -d plt=$PLTHOME
hash -d tests=~plt/collects/tests
hash -d ws=~plt/collects/web-server
hash -d drdr=~plt/collects/meta/drdr
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

hash -d fspec=~scm/svn.smc-lab/students/MS/morse-everett/fspec/trunk
hash -d uber-lazy=~scm/svn.smc-lab/students/PhD/rungta-neha/papers/uber-lazy/trunk

hash -d courses=~work/courses
hash -d 630=~courses/2013/spring/630
hash -d 430=~courses/2013/winter/430
hash -d 330=~courses/2012/fall/330

export PATH=~exp/bin:~work/papers/etc/bin:$PATH

setopt autopushd pushdminus pushdsilent pushdtohome

autoload -U zmv
bindkey -e

export PS1="%S%~%s
%# "
TPS1="%~ %# "
RECENTFILES=8

# Interaction with Emacs:
function set-eterm-dir {
    echo -e "\033AnSiTu" "$LOGNAME" # $LOGNAME is more portable than using whoami.
    echo -e "\033AnSiTc" "$(pwd)"
    if [ $(uname) = "SunOS" ]; then
	    # The -f option does something else on SunOS and is not needed anyway.
       	hostname_options="";
    else
        hostname_options="-f";
    fi
    echo -e "\033AnSiTh" "$(hostname $hostname_options)" # Using the -f option can cause problems on some OSes.
}

        # Track directory, username, and cwd for remote logons.
if [ "$TERM" = "eterm-color" ]; then
    precmd () { set-eterm-dir }
elif [[ "$TERM" =~ "screen" ]] ; then
    precmd () {print -Pn "\e]0;$TPS1\a\033k$TPS1\033\\"}
    preexec () {print -Pn "\e]0;$TPS1 $2\a\033k$TPS1 $2\033\\"}
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
    ls -t | head -$RECENTFILES | tr '\n' '\0' | xargs -0 ls -d --color=auto
}

if [ $(pwd) = ${HOME} ] ; then
    read_zdir
fi

# Completions
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
#zstyle ':completion:*' use-cache on
#zstyle ':completion:*' cache-path ~/.zsh/cache

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
    scp -r $1 weapons.cs.byu.edu:public_html/tmp/${NAME}
    echo http://faculty.cs.byu.edu/~jay/tmp/${NAME}
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


PATH=$PATH:$HOME/.rvm/bin # Add RVM to PATH for scripting

if [ -L ~/.racket/doc ] ; then
    rm ~/.racket/doc
    ln -s $(racket -e '(require setup/dirs) (displayln (path->string (find-user-doc-dir)))') ~/.racket/doc
fi
