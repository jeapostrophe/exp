#lang typed/racket

(: f ((Listof Float) -> Float))
(define (f l)
  (cond
    [(empty? l)
     0.0]
    [else
     (+ (first l)
        (f (rest l)))]))

(provide f)
