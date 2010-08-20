#lang racket
;; Compiler
(require syntax/parse)

(define-syntax-class nonterminal-def
  (pattern (nt:id v:redex-pattern ...)
           #:attr id #'nt
           #:attr variants (syntax->list #'(v ...))))

(define (num stx) (error))
(define (hole stx) (error))

(define-syntax-class redex-pattern
  #:literals ([num num #:phase 1]
              [hole hole #:phase 1])
  (pattern num
           #:attr type 'number)
  (pattern hole
           #:attr type 'hole)
  (pattern some-id:id
           #:attr type 'id
           #:attr value #'some-id)
  (pattern (p:redex-pattern ...)
           #:attr type 'nested
           #:attr value #'(p ...)))

(provide nonterminal-def
         redex-pattern
         num hole)