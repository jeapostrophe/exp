#lang racket
(require "nfa.rkt"
         (for-syntax syntax/parse
                     unstable/syntax))

(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))

(define-for-syntax (compile-regex start e end)
  (syntax-parse
   e
   #:literals (seq union *)
   [(* lhs:expr)
    (with-syntax*
        ([start_lhs (generate-temporary 'start_lhs)])
      (quasisyntax/loc e
        ([#,start ([epsilon (start_lhs #,end)])]
         #,@(compile-regex #'start_lhs #'lhs start))))]
   [(seq lhs:expr rhs:expr)
    (with-syntax*
        ([start_rhs (generate-temporary 'start_rhs)])
      (quasisyntax/loc e
        (#,@(compile-regex start #'lhs #'start_rhs)
         #,@(compile-regex #'start_rhs #'rhs end))))]
   [(seq lhs:expr rest:expr ...)
    (compile-regex start #'(seq lhs (seq rest ...)) end)]
   [(union lhs:expr rhs:expr)
    (with-syntax*
        ([start_lhs (generate-temporary 'start_lhs)]
         [start_rhs (generate-temporary 'start_rhs)])
      (quasisyntax/loc e
        ([#,start ([epsilon (start_lhs start_rhs)])]
         #,@(compile-regex #'start_lhs #'lhs end)
         #,@(compile-regex #'start_rhs #'rhs end))))]
   [(union lhs:expr rest:expr ...)
    (compile-regex start #'(union lhs (union rest ...)) end)]
   [pat:expr
    (quasisyntax/loc e
      ([#,start ([pat (#,end)])]))]))

(define-syntax (regex stx)
  (syntax-parse
   stx
   [(_ e:expr)
    (with-syntax*
        ([start (generate-temporary 'start)]
         [end (generate-temporary 'end)])
      (quasisyntax/loc stx
        (nfa start (end)
             #,@(compile-regex #'start #'e #'end))))]))

(define regex-accepts? nfa-accepts?)  

(require tests/eli-tester)
(define M
  (regex (union (seq (* 1) (* (seq 0 (* 1) 0 (* 1))))
                (seq (* 0) (* (seq 1 (* 0) 1 (* 0)))))))
(test
 (regex-accepts? M (list 1 0 1 0 1))
 (regex-accepts? M (list 0 1 0 1 0))
 (regex-accepts? M (list 1 0 1 1 0 1))
 (regex-accepts? M (list 0 1 0 0 1 0))
 (regex-accepts? M (list))
 (regex-accepts? M (list 1 0)) => #f)
