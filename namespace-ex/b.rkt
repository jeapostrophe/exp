#lang racket
(require "common.rkt" "a.rkt")
(define (g a) 0)
(provide/contract
 [g (-> foo? number?)])