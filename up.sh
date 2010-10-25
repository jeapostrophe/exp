#!/bin/zsh
log=~/.up.log
. ~/.zshrc &>/dev/null

cd ~/Dev/scm &>/dev/null

do_dir () {
    dir=$1
    f=$2
    if [ -d "${dir}" ] ; then
	pushd "${dir}" &>/dev/null
	echo "${dir}... "
	while ! $f &> ${log} ; do
	    cat ${log}
	    zsh
	done
	popd &>/dev/null
    fi
}

cvs_up () { cvs up }
svn_up () { #svn up
echo }
git_up () { git up && git push }

for i in cvs.* ; do
    do_dir $i cvs_up
done

for i in svn.* ; do
    do_dir $i svn_up
done

for i in github.*/* usr.plt/*/* ; do
    do_dir $i git_up
done
