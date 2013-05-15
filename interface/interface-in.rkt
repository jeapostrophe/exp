#lang racket
(require "interface.rkt"
         "interface-def.rkt"
         (interface-in listy!
                       "interface-out.rkt")
         rackunit)

(check-false (kons? 1))
(define x (kons 1 2))
(check-true (kons? x))
(check-equal? (kar x) 1)
(check-equal? (kdr x) 2)
