from aqt import mw
from aqt.utils import showInfo
from aqt.qt import *

def monster():
    newCount, lrnCount, revCount = mw.col.sched.counts()
    totalCount = (newCount + lrnCount + revCount)
    howManyToDo = totalCount / 2
    if howManyToDo < 50:
        howManyToDo = 50
    if totalCount < 50:
        howManyToDo = totalCount

    mw.reviewer.nextCard()

action = QAction("Monster", mw)
mw.connect(action, SIGNAL("triggered()"), monster)
mw.form.menuTools.addAction(action)
