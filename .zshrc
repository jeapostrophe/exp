source ~/.zshrc-dirs

setopt inc_append_history share_history
setopt printeightbit
setopt autopushd pushdminus pushdsilent pushdtohome

bindkey -e # emacs key bindings

export REPORTTIME=10

PROMPT_SYMB=❯
PROMPT_SYMB=⌁
PROMPT_SYMB=►
PROMPT_SYMB=⫸
PROMPT_SYMB="🍔 " # Hamburger
PROMPT_SYMB="🍕 " # Pizza
PROMPT_SYMB="👾 " # Space Invader
PROMPT_SYMB="💩 " # Poop

PROMPT_SYMB=⫸
PS1="%(?.%F{green}.%F{red})${PROMPT_SYMB}%f "

if [[ "$TMUX" == "" ]] ; then
    PS1="%S%~%s
$PS1"
fi
export PS1

TPS1="%~ ${PROMPT_SYMB}"

precmd () {
    print -Pn "\e]0;$TPS1\a"
#    print -Pn "\033k$TPS1\033\\"
}
preexec () {
    print -Pn "\e]0;$TPS1 $2\a"
#    print -Pn "\033k$TPS1 $2\033\\"
}

chpwd() {
    recent dir "$PWD"
}

