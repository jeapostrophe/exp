#lang racket/base
(require racket/match
         racket/list)

(define-syntax-rule (evt-regexp evts pat ...)
  (match evts [(list pat ...) #t] [_ #f]))
(provide evt-regexp)

(define (make-trace-predicate ?)
  (define evts empty)
  (λ (evt)
    (set! evts (cons evt evts))
    (? evts)))
(provide make-trace-predicate)