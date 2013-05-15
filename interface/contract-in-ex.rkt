#lang racket
(require
 "contract-in.rkt"
 (contract-in
  "contract-in-def.rkt"
  [f (-> number? number?)]
  [g (-> number? number?)])
 rackunit)

(check-not-exn (λ () (f 1)))
(check-exn exn:fail:contract?
           (λ () (f "zero")))
(check-exn exn:fail:contract?
           (λ () (g 0)))
