#!/usr/bin/env python
class Empty:
    def __init__(this):
        return

    def __str__(this):
        return "Empty()"

    def insertAt(this, n, k):
        return Cons(k, this)

class Cons:
    def __init__(this, first, rest):
        this.first = first
        this.rest = rest
        return

    def __str__(this):
        return "Cons(" + str(this.first) + ", " + str(this.rest) + ")"

    def insertAt(this, n, k):
        if n <= 0:
            return Cons(k, this)
        else:
            return Cons(this.first, this.rest.insertAt(n - 1, k))

class Zipper:
    def __init__(this, before, after):
        this.before = before
        this.after = after

    def __str__(this):
        return "Zipper(" + str(this.before) + ", " + str(this.after) + ")"

    def right(this):
        return Zipper(Cons(this.after.first, this.before), this.after.rest)

    def insert(this, k):
        return Zipper(this.before, Cons(k, this.after))

    def left(this):
        return Zipper(this.before.rest, Cons(this.before.first, this.after))

    def list(this):
        return this.after

def zipper(l):
    return Zipper(Empty(), l)

def main():
    l = Cons(0, Cons(1, Cons(2, Cons(3, Cons(4, Empty())))))
    print "      l = " + str(l)
    
    lp = l.insertAt(3, 2.9)
    print "      l = " + str(l)
    print "     lp = " + str(lp)
    
    lpp = lp.insertAt(3, 2.8)
    print "    lpp = " + str(lpp)
    
    z = zipper(l)
    print "      z = " + str(z)
    spot = z.right().right().right()
    print "   spot = " + str(spot)
    spotp = spot.insert(2.9)
    print "  spotp = " + str(spotp)
    spotpp = spotp.insert(2.8)
    print " spotpp = " + str(spotpp)
    zp = spotpp.left().left().left()
    print "     zp = " + str(zp)
    lppp = zp.list()
    print "   lppp = " + str(lppp)
    
if __name__ == "__main__":
    main()
