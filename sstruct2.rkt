#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/list)

(begin-for-syntax
  (define-syntax-class formals
    [pattern rest:id]
    [pattern (mandatory:id . rest:formals)]
    [pattern ()])
  (define-syntax-class option))

(define-syntax (sstruct stx)
  (syntax-parse stx
    [(_ (n:id . h:formals) o:option ...)
     (syntax/loc stx
       (begin
         (define-values (n:type n:constructor n? n:accessor n:mutator)
           (make-struct-type 'n #f 0 0 #f empty (current-inspector) #f empty #f 'n))))]))

(module+ test
  (require rackunit)

  (let ()
    (sstruct (posn x y))
    (define p0 (posn 1 2))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2))

  (let ()
    (sstruct (posn x y)
             #:accessor "posn.~a")
    (define p0 (posn 1 2))
    (check-equal? (posn.x p0) 1)
    (check-equal? (posn.y p0) 2)))
