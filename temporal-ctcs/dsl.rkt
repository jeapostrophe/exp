#lang racket/base
(require racket/match
         racket/stxparam
         (for-syntax racket/base)
         "temporal.rkt"
         "automata3/re.rkt"
         "automata3/re-ext.rkt")
(provide call ret monitor n->
         (all-from-out 
          "automata3/re.rkt"
          "automata3/re-ext.rkt"))

(define-syntax-parameter stx-monitor-id 
  (λ (stx) (raise-syntax-error 'n-> "Used outside monitor" stx)))

(define-syntax-rule (n-> n K_1 ... K_2)
  (->t stx-monitor-id n K_1 ... K_2))

(define-syntax-rule (monitor K T)
  (let ([monitor (re->evt-predicate (re T))])
    (syntax-parameterize ([stx-monitor-id (make-rename-transformer #'monitor)])
                         K)))

(define (re->evt-predicate m)
  (define current-re m)
  (λ (evt)
    #;(printf "~S\n" evt)
    (set! current-re (current-re evt))
    (re-accepting? current-re)))

(define-match-expander call
  (syntax-rules ()
    [(_ n p ...)
     (evt:call n _ _ _ _ _ (list p ...))]))

(define-match-expander ret
  (syntax-rules ()
    [(_ n p ...)
     (evt:return n _ _ _ _ _ _ (list p ...))]))
