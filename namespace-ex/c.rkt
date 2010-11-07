#lang racket
(require "common.rkt" "b.rkt")
(define (go f)
  (g (f)))

; Swap the provides to see a strange effect
(provide go)

#;(provide/contract
 [go (-> (-> foo?) number?)])