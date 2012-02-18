#!/usr/bin/zsh
. ~/.zshrc
export DISPLAY=0.0
export XAUTHORITY=~/.Xauthority

chpwd () {}

for REPO in ~exp ~home ~work ; do
    cd $REPO
    # Remove deleted files
    git ls-files --deleted -z | xargs -0 git rm >/dev/null 2>&1
    # Add new files
    git add . >/dev/null 2>&1
    git commit -m "Automatic commit at $(date)"
    git push
done

