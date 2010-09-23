source ~/.profile

hash -d scm=$SVNROOT
hash -d plt=$PLTHOME
hash -d ws=~plt/collects/web-server
hash -d drdr=~plt/collects/meta/drdr
hash -d work=$PROJS
hash -d papers=~work/papers
hash -d planet=~scm/github.jeapostrophe.planet
hash -d github=~scm/github.jeapostrophe
hash -d exp=~scm/github.jeapostrophe/exp
hash -d fin=~scm/github.jeapostrophe/home/finance
hash -d uber-lazy=~scm/svn.smc-lab/students/PhD/rungta-neha/papers/uber-lazy/trunk

export PATH=~work/papers/etc/bin:$PATH

setopt autopushd pushdminus pushdsilent pushdtohome

autoload -U zmv
autoload -U compinit
compinit 

export PS1="%S%~%s
%# "
TPS1="%~ %# "
RECENTFILES=8

precmd () {print -Pn "\e]0;$TPS1\a"}
preexec () {print -Pn "\e]0;$TPS1 $2\a"}

ZDIRS=~/.zdirs

# Read in ZDIRS
write_zdirs () {
    dirs -lp >! $ZDIRS
}

# Read in ZDIRS
read_zdirs () {
    dirstack=()
    while IFS= read -r line ; do
	dirstack+=($line)
    done < $ZDIRS
    popd
}

chpwd () {
    # Save what directory we are in for the future
    write_zdirs
    # Show recently modified files
    ls -t | head -$RECENTFILES | tr '\n' '\0' | xargs -0 ls -d
}

read_zdirs

# Completions
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

# Nice chdir
cdirs () {
    dirs -lp | sort | uniq -c | sort -nr | sed 's/^ *[0-9]* *//'
}

c () {
    if [ "$1" = "" ] ; then
	cdirs | cat -n
    elif [[ "$1" = <-> ]] ; then
	read_cdirs_into_reply
	cd $reply[$1]
    else
	cd "$1"
    fi
}

read_cdirs_into_reply () {
    while IFS= read -r line ; do
	reply+=($line)
    done < <(cdirs)
}

compctl -Q -K read_cdirs_into_reply c
