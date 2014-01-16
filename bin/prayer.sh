#!/bin/zsh
. ~/.zshrc

DEST=~blogs/jeapstrophe.github.com-ng/blog/family

racket -t ~exp/prayer.rkt
for i in prayer.json prayer.js prayer.html ; do
    cp ~exp/${i} $DEST
done
cd $DEST
git add .
git commit -m "prayer" . || true
git push
git gc
