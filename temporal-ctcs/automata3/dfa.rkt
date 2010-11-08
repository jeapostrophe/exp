#lang racket/base
(require "machine.rkt"
         racket/contract
         racket/match
         racket/set)

(struct dfa (delta start accepting) #:transparent)

(define (dfa->machine d)
  (match-define (dfa delta start accepting) d)
  (define (state->machine start)
    (λ (a)
      (define next (delta start a))
      (define accepting? (set-member? next accepting))
      (values accepting (state->machine next))))
  (state->machine start))

(define state/c any/c)
(define input/c any/c)
(define (set/c elem/c) set?)
(provide/contract
 [struct dfa ([delta (-> state/c input/c state/c)]
              [start state/c]
              [accepting (set/c state/c)])]
 [dfa->machine (dfa? . -> . accepting-machine/c)])