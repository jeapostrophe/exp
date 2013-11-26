#lang racket/base

(struct promise (actual-value maker) #:mutable)
(define (delay* t)
  (define (maker)
    (set-promise-actual-value! p (t))
    (set-promise-maker! p #f))
  (define p (promise #f maker))
  p)
(define-syntax-rule (delay e)
  (delay* (λ () e)))
(define (force p)
  (when (promise-maker p)
    ((promise-maker p)))
  (promise-actual-value p))

;;.....

(define ones
  (cons 1 (delay ones)))
(car ones)
(car (force (cdr ones)))

(define (forcing-list-ref l i)
  (if (promise? l)
    (forcing-list-ref (force l) i)
    (if (zero? i)
      (car l)
      (forcing-list-ref (cdr l) (sub1 i)))))

(forcing-list-ref ones 50)
