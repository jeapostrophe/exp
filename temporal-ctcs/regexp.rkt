#lang racket
(require "nfa.rkt"
         (for-syntax syntax/parse
                     unstable/syntax))

(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))

(define-for-syntax (compile-regex e)
  (syntax-parse
   e
   #:literals (seq union *)
   [(* lhs:expr)
    (with-syntax*
        ([start_* (generate-temporary 'start_*)]
         [(_ start_l (end_l ...)
             [state_l ([input_l (next-state_l ...)]
                       ...)]
             ...)
          (compile-regex #'lhs)])
      (syntax/loc e
        (nfa start_* (start_*)
             [start_* ([epsilon (start_l)])]
             
             [state_l ([input_l (next-state_l ...)]
                        ...)]
             ...
             [end_l ([epsilon (start_*)])]
             ...)))]
   [(seq lhs:expr rhs:expr)
    (with-syntax*
        ([start_seq (generate-temporary 'start_seq)]
         [end_seq (generate-temporary 'end_seq)]
         [(_ start_l (end_l ...)
             [state_l ([input_l (next-state_l ...)]
                       ...)]
             ...)
          (compile-regex #'lhs)]
         [(_ start_r (end_r ...)
             [state_r ([input_r (next-state_r ...)]
                       ...)]
             ...)
          (compile-regex #'rhs)])
      (syntax/loc e
        (nfa start_seq (end_seq)
             [start_seq ([epsilon (start_l)])]
             
             
             [state_l ([input_l (next-state_l ...)]
                        ...)]
             ...
             [end_l ([epsilon (start_r)])]
             ...
             [state_r ([input_r (next-state_r ...)]
                       ...)]
             ...
             [end_r ([epsilon (end_seq)])]
             ...)))]
   [(seq lhs:expr rest:expr ...)
    (compile-regex #'(seq lhs (seq rest ...)))]
   [(union lhs:expr rhs:expr)
    (with-syntax*
        ([start_union (generate-temporary 'start_union)]
         [end_union (generate-temporary 'end_union)]
         [(_ start_l (end_l ...)
             [state_l ([input_l (next-state_l ...)]
                       ...)]
             ...)
          (compile-regex #'lhs)]
         [(_ start_r (end_r ...)
             [state_r ([input_r (next-state_r ...)]
                       ...)]
             ...)
          (compile-regex #'rhs)])
      (syntax/loc e
        (nfa start_union (end_union)
             [start_union ([epsilon (start_l start_r)])]
             
             [state_l ([input_l (next-state_l ...)]
                        ...)]
             ...
             [state_r ([input_r (next-state_r ...)]
                       ...)]
             ...
             
             [end_l ([epsilon (end_union)])]
             ...
             [end_r ([epsilon (end_union)])]
             ...)))]
   [(union lhs:expr rest:expr ...)
    (compile-regex #'(union lhs (union rest ...)))]
   [pat:expr
    (with-syntax*
        ([start_pat (generate-temporary 'start_pat)]
         [end_pat (generate-temporary 'end_pat)])
      (syntax/loc e
        (nfa start_pat (end_pat)
             [start_pat ([pat (end_pat)])])))]))

(define-syntax (regex stx)
  (syntax-parse
   stx
   [(_ e:expr)
    (compile-regex #'e)]))

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
