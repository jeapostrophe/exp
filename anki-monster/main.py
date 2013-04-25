from anki.hooks import addHook
from aqt import mw
from aqt.utils import showInfo
from aqt.qt import *
import os, random
from random import shuffle

N = 50
MonstersPath = os.path.join(os.path.expanduser("~"), "Downloads", "anki-monster-pngs")

def loadMonster(png):
    path = os.path.join( MonstersPath, png )
    pixmap = QPixmap(path, "png")
    return pixmap

def monster():
    newCount, lrnCount, revCount = mw.col.sched.counts()
    totalCount = (newCount + lrnCount + revCount)
    howManyToDo = totalCount / 2
    if howManyToDo < N:
        howManyToDo = N
    if totalCount < N:
        howManyToDo = totalCount

    mw.monstersToDo = howManyToDo
    mw.monstersDone = 0
    # XXX If howManyToDo is > than the number of pngs, this is bad
    mw.monsters = [ loadMonster(png) for png in os.listdir(MonstersPath)]
    shuffle(mw.monsters)

    if mw.monstersToDo > 0:
        displayMonsters(False)
        mw.moveToState("review")

def setScaledPixmap(l, w, h, p):
    sp = p.scaled(w, h, Qt.KeepAspectRatio)
    l.setPixmap(sp)

def displayMonsters(shoot_p):
    parent = mw.app.activeWindow() or mw

    w = parent.size().width()
    h = parent.size().height()

    mb = QDialog(parent)
    mb.setWindowModality(Qt.WindowModal)

    grid = QGridLayout()

    grid.setMargin(1)
    grid.setVerticalSpacing(1)
    grid.setHorizontalSpacing(1)

    monster_h = h / 3
    monster_w = w / (mw.monstersToDo + mw.monstersDone + 1)
    monster_align = (Qt.AlignHCenter) | ( Qt.AlignBottom )

    grid.setRowMinimumHeight(0, monster_h)
    grid.setRowMinimumHeight(1, monster_h)

    # XXX The drawings are ugly, because of the black background

    dead = QLabel("Dead")
    grid.addWidget( dead, 0, 0, 1, 1, Qt.AlignCenter )
    for i in xrange(mw.monstersDone):
        l = QLabel()
        setScaledPixmap( l, monster_w, monster_h, mw.monsters[ i ] )
        grid.addWidget( l, 0, i + 1, monster_align )

    alive = QLabel("Alive")
    grid.addWidget( alive, 1, 0, 1, 1, Qt.AlignCenter )
    for i in xrange(mw.monstersToDo):
        l = QLabel()
        setScaledPixmap( l, monster_w, monster_h, mw.monsters[ mw.monstersDone + i ] )
        grid.addWidget( l, 1, i + 1, monster_align )

    b = QPushButton("Shoot" if shoot_p else "Next")
    b.setDefault(True)
    mb.connect(b, SIGNAL('clicked()'), mb.accept)
    grid.addWidget( b, 2, 0, 1, -1, Qt.AlignCenter )

    mb.setLayout(grid)
    mb.exec_()

def monsterAnswerCard(card, ease):
    if ease == 1:
        return

    displayMonsters(True)

    mw.monstersDone = mw.monstersDone + 1
    mw.monstersToDo = mw.monstersToDo - 1

    displayMonsters(False)

    if mw.monstersToDo <= 0:
        mw.moveToState("deckBrowser")

addHook('answerCard', monsterAnswerCard)

action = QAction("Monster", mw)
mw.connect(action, SIGNAL("triggered()"), monster)
mw.form.menuTools.addAction(action)
