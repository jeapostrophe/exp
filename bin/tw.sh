#!/usr/bin/zsh
. ~/.zshrc

precmd () {}
preexec () {}
chpwd () {}

python2 ~exp/tw.py
scp -r ~/Downloads/rss y:public_html
