#lang racket/base
(module+ main
  (require rackunit)
  (let ()
    (local-require "tr-cheat-tr.rkt")
    (check-exn exn:fail:contract?
               (λ () (f (vector 1 2 3)))))

  (let ()
    (local-require "tr-cheat-ex.rkt")
    (local-require "tr-cheat-tr2.rkt")
    (check-exn exn:fail:contract?
               (λ () (g (vector 1 2 3))))
    (f (vector 1 2 3))))
