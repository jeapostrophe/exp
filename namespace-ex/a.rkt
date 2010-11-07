#lang racket
(require "common.rkt")
(define (f) (foo))
(provide/contract
 [f (-> foo?)])