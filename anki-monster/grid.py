#!/usr/bin/env python2
# -*- coding: utf-8 -*-

"""
ZetCode PyQt4 tutorial 

In this example, we create a skeleton
of a calculator using a QtGui.QGridLayout.

author: Jan Bodnar
website: zetcode.com 
last edited: October 2011
"""

import sys
from PyQt4 import QtGui, Qt


class Example:
    
    def __init__(self):
        self.initUI()
        
    def initUI(self):
        self.qw = QtGui.QDialog();
        self.qw.setWindowModality(1)
        
        names = ['Cls', 'Bck', '', 'Close', '7', '8', '9', '/',
                '4', '5', '6', '*', '1', '2', '3', '-',
                '0', '.', '=', '+']

        grid = QtGui.QGridLayout()

        j = 0
        pos = [(0, 0), (0, 1), (0, 2), (0, 3),
                (1, 0), (1, 1), (1, 2), (1, 3),
                (2, 0), (2, 1), (2, 2), (2, 3),
                (3, 0), (3, 1), (3, 2), (3, 3 ),
                (4, 0), (4, 1), (4, 2), (4, 3)]

        for i in names:
            button = QtGui.QPushButton(i)
            if j == 2:
                grid.addWidget(QtGui.QLabel(''), 0, 2)
            else:
                grid.addWidget(button, pos[j][0], pos[j][1])
            if i == 'Close':
                button.setDefault(True)
                self.qw.connect(button, Qt.SIGNAL('clicked()'), self.qw.accept)
            j = j + 1

        self.qw.setLayout(grid)   
        
        self.qw.exec_()
        
def main():
    
    app = QtGui.QApplication(sys.argv)
    ex = Example()
    sys.exit(app.exec_())


if __name__ == '__main__':
    main()
