#lang racket/base
(require "re.rkt"
         (for-syntax syntax/parse
                     racket/base))

(define-re-transformer opt
  (syntax-rules ()
    [(_ pat)
     (union epsilon pat)]))
(define-re-transformer plus
  (syntax-rules ()
    [(_ pat)
     (seq pat (star pat))]))
(define-re-transformer rep
  (syntax-parser
   [(_ pat k:number)
    (with-syntax
        ([(pat_i ...) (build-list (syntax->datum #'k) (λ (i) #'pat))])
      #'(seq pat_i ...))]))
(define-re-transformer difference
  (syntax-rules ()
    [(_ A B)
     (intersection A (complement B))]))
(define-re-transformer intersection
  (syntax-rules ()
    [(_ A B)
     (complement (union (complement A) (complement B)))]))

(provide opt plus rep difference intersection)