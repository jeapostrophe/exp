#lang racket
(require "nfa-ep.rkt"
         (for-syntax syntax/parse
                     unstable/syntax))

(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))

; compile-regex : pattern end-state-id -> (values start-state-id nfa-states)
; compile-regex MUST NOT create end
(define-for-syntax (compile-regex e ends)
  (syntax-parse
   e
   #:literals (seq union *)
   [(* lhs:expr)
    (define start (generate-temporary 'start))
    (define-values (start_lhs lhs-states) (compile-regex #'lhs (list start)))
    (values
     (list start)
     (quasisyntax/loc e
       ([#,start ([epsilon (#,@start_lhs #,@ends)])]
        #,@lhs-states)))]
   [(seq lhs:expr rhs:expr)
    (define-values (start_rhs rhs-states) (compile-regex #'rhs ends))
    (define-values (start_lhs lhs-states) (compile-regex #'lhs start_rhs))
    (values start_lhs
            (quasisyntax/loc e
              (#,@lhs-states
               #,@rhs-states)))]
   [(seq lhs:expr rest:expr ...)
    (compile-regex #'(seq lhs (seq rest ...)) ends)]
   [(union lhs:expr rhs:expr)
    (define-values (start_lhs lhs-states) (compile-regex #'lhs ends))
    (define-values (start_rhs rhs-states) (compile-regex #'rhs ends))
    (values (append start_lhs start_rhs)
            (quasisyntax/loc e
              (#,@lhs-states
               #,@rhs-states)))]
   [(union lhs:expr rest:expr ...)
    (compile-regex #'(union lhs (union rest ...)) ends)]
   [pat:expr
    (define start (generate-temporary #'pat))
    (values (list start)
            (quasisyntax/loc e
              ([#,start ([pat (#,@ends)])])))]))

(define-syntax (regex stx)
  (syntax-parse
   stx
   [(_ e:expr)
    (define end (generate-temporary 'end))
    (define-values (starts e-states) (compile-regex #'e (list end)))
    (quasisyntax/loc stx
      (nfa/ep (#,@starts) (#,end)
              #,@e-states
              [#,end ()]))]))

(define regex-accepts? nfa/ep-accepts?)  

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
