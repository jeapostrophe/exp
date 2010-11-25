#!/usr/bin/python

def fun(a,b,c):
    if a:
        print "a"
    elif b:
        print "b"
    elif c:
        print "c"

fun(True, False, False)

fun(False, True, False)

fun(False, False, True)

fun(True, True, 1/0)
