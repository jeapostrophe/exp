#lang racket/base
(require racket/match
         racket/stxparam
         (for-syntax racket/base)
         "monitor.rkt"
         "automata/re.rkt"
         "automata/re-ext.rkt")
(provide call ret with-monitor label
         (all-from-out 
          "automata/re.rkt"
          "automata/re-ext.rkt"))

(define-syntax-parameter stx-monitor-id 
  (λ (stx) (raise-syntax-error 'label "Used outside monitor" stx)))

(define-syntax-rule (label n K)
  (monitor/c stx-monitor-id n K))

(define-syntax with-monitor
  (syntax-rules ()
    [(_ K)
     (let ([monitor (λ (x) #t)])
       (syntax-parameterize ([stx-monitor-id (make-rename-transformer #'monitor)])
                            K))]
    [(_ K T)
     (let ([monitor (re->evt-predicate (re T))])
       (syntax-parameterize ([stx-monitor-id (make-rename-transformer #'monitor)])
                            K))]))

(define (re->evt-predicate m)
  (define current-re m)
  (λ (evt)
    #;(printf "~S\n" evt)
    (set! current-re (current-re evt))
    (re-accepting? current-re)))

(define-match-expander call
  (syntax-rules ()
    [(_ n p ...)
     (evt:call n _ _ _ (list p ...))]))

(define-match-expander ret
  (syntax-rules ()
    [(_ n p ...)
     (evt:return n _ _ _ _ (list p ...))]))
