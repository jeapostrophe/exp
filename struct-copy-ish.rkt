#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match)

(begin-for-syntax
  (define-syntax-class structb
    (pattern n
             #:declare n (static struct-info? "structure binding"))))

(define-syntax (struct-copy-ish stx)
  (syntax-parse stx
    [(_ top:structb (mid:structb ...)
        e:expr
        [f:id fe:expr]
        ...)
     (syntax/loc stx
       )]))

;; example
(module+ test
  (struct posn (x y))
  (struct 3posn posn (z))

  (define e1 (3posn 1 2 3))
  (define e2 (struct-copy-ish posn (3posn) e1 [x 5]))
  
  (check-equal? (posn-x e2) 5)
  (check-equal? (posn-y e2) 2)
  (check-equal? (3posn-z e2) 3))
