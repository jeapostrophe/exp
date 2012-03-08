#!/usr/bin/zsh
. ~/.zshrc

chpwd () {}

python ~exp/tw.py
scp -r ~/Downloads/rss y:public_html
