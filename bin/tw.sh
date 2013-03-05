#!/usr/bin/zsh
. ~/.zshrc

precmd () {}
preexec () {}
chpwd () {}

if netcfgd pstatus | grep up &> /dev/null ; then
    python2 ~exp/tw.py
    rk ~exp/sda.rkt ~/Downloads/rss/sda.xml
    scp -r ~/Downloads/rss y:public_html
fi
