#lang racket
(require "dfa.rkt")

(require tests/eli-tester)
(define M
  (dfa s1
       ([s1 ([0 s2]
             [1 s1])])
       ([s2 ([0 s1]
             [1 s2])])))

(test
 (dfa-accepts? M (list 1 0 1 0 1))
 (dfa-accepts? M (list 1 0 1 1 0 1))
 (dfa-accepts? M (list 0 1 0 0 1 0))
 (dfa-accepts? M (list))
 (dfa-accepts? M (list 1 0)) => #f)