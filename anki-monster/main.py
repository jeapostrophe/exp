from anki.hooks import addHook
from aqt import mw
from aqt.utils import showInfo
from aqt.qt import *

N = 50

def monster():
    newCount, lrnCount, revCount = mw.col.sched.counts()
    totalCount = (newCount + lrnCount + revCount)
    howManyToDo = totalCount / 2
    if howManyToDo < N:
        howManyToDo = N
    if totalCount < N:
        howManyToDo = totalCount

    mw.monsterToDo = howManyToDo

    if mw.monsterToDo > 0:
        mw.moveToState("review")

# XXX Either put a display of monster into the Web view here:
def monsterShowQuestion():
    showInfo("Current monsters: %d" % mw.monsterToDo)

addHook('showQuestion', monsterShowQuestion)

# XXX Or, make it so if we don't return, then display the set of monsters

def monsterAnswerCard(card, ease):
    if ease == 1:
        return

    mw.monsterToDo = mw.monsterToDo - 1

    if mw.monsterToDo <= 0:
        mw.moveToState("deckBrowser")

addHook('answerCard', monsterAnswerCard)

action = QAction("Monster", mw)
mw.connect(action, SIGNAL("triggered()"), monster)
mw.form.menuTools.addAction(action)
