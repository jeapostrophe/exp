#lang racket
(require "regexp.rkt"
         (for-syntax syntax/parse
                     racket/list
                     racket/match
                     "regexp-help.rkt"
                     unstable/syntax))

(define-regex-transformer opt
  (syntax-rules ()
    [(_ pat)
     (union epsilon pat)]))
(define-regex-transformer plus
  (syntax-rules ()
    [(_ pat)
     (seq pat (star pat))]))
(define-regex-transformer rep
  (syntax-parser
   [(_ pat k:number)
    (with-syntax
        ([(pat_i ...) (build-list (syntax->datum #'k) (λ (i) #'pat))])
      #'(seq pat_i ...))]))
(define-regex-transformer never
  (syntax-parser
   [x:id #'(plus (and 1 (not 1)))]))
(define-regex-transformer difference
  (syntax-rules ()
    [(_ A B)
     (intersection A (complement B))]))
(define-regex-transformer intersection
  (syntax-rules ()
    [(_ A B)
     (complement (union (complement A) (complement B)))]))

(provide opt plus rep never difference intersection)