#lang racket/base

(module+ test
  (let ()
    (sstruct (posn x y))
    (define p0 (posn 1 2))
    (check-equal? (posn.x p0) 1)
    (check-equal? (posn.x p0) 2)))
