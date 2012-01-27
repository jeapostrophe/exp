#lang racket/base
(require "org.rkt")

(define ex "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
(write-org
 (with-input-from-file ex read-org))

;; XXX Go through and give everything an id
;; XXX Store a database of <= elements
;; XXX Request X of them when run
;; XXX Produce sorted list
