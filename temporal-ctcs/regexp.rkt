#lang racket
(require "nfa-ep.rkt"
         "regexp-help.rkt"
         (for-syntax syntax/parse
                     racket/list
                     "regexp-help.rkt"
                     unstable/syntax))

; XXX do and, complement, difference

(define-syntax-rule (define-regex-transformer id lam)
  (define-syntax id (regex-transformer lam)))

(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))
(define-syntax (star stx) (raise-syntax-error 'star "Outside regex" stx))

; compile-regex : pattern end-state-ids -> (values start-state-ids nfa-states)
; compile-regex MUST NOT create end and MUST return start-state-ids that exist
(define-for-syntax (compile-regex e ends)
  (syntax-parse
   e
   #:literals (seq union star epsilon)
   [(star lhs:expr)
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
   [(~var transformer (static regex-transformer? "regex transformer"))
    (compile-regex ((regex-transformer->regex (attribute transformer.value)) e) ends)]
   [((~var transformer (static regex-transformer? "regex transformer")) . _)
    (compile-regex ((regex-transformer->regex (attribute transformer.value)) e) ends)]
   [epsilon
    (values ends
            empty)]
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

(define regex-advance nfa/ep-advance)
(define regex-accepting? nfa/ep-accepting?)
(define regex-accepts? nfa/ep-accepts?)

(provide
 seq union star epsilon
 define-regex-transformer
 regex
 regex-advance
 regex-accepting?
 regex-accepts?)

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
    [x:id #'(and 1 (not 1))]))

(provide opt plus rep never)

(require tests/eli-tester)
(define M
  (regex (seq epsilon
              (union (seq (star 1) (star (seq 0 (star 1) 0 (star 1))))
                     (seq (star 0) (star (seq 1 (star 0) 1 (star 0)))))
              epsilon)))
(define N
  (regex (seq "A" (opt "B"))))
(define O
  (regex (plus "A")))
(define P
  (regex (rep "A" 3)))
(define Q
  (regex never))
(test
 (regex-accepts? Q (list)) => #f
 (regex-accepts? Q (list "A")) => #f
 (regex-accepts? N (list "A"))
 (regex-accepts? N (list "A" "B"))
 (regex-accepts? N (list "A" "B" "C")) => #f
 (regex-accepts? O (list)) => #f
 (regex-accepts? O (list "A"))
 (regex-accepts? O (list "A" "A"))
 (regex-accepts? P (list)) => #f
 (regex-accepts? P (list "A")) => #f
 (regex-accepts? P (list "A" "A")) => #f
 (regex-accepts? P (list "A" "A" "A"))
 (regex-accepts? M (list 1 0 1 0 1))
 (regex-accepts? M (list 0 1 0 1 0))
 (regex-accepts? M (list 1 0 1 1 0 1))
 (regex-accepts? M (list 0 1 0 0 1 0))
 (regex-accepts? M (list))
 (regex-accepts? M (list 1 0)) => #f)
