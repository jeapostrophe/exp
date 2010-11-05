#lang racket
(require "nfa-ep.rkt"
         "regexp-help.rkt"
         (for-syntax syntax/parse
                     racket/list
                     racket/match
                     "regexp-help.rkt"
                     unstable/syntax))

(define-syntax-rule (define-regex-transformer id lam)
  (define-syntax id (regex-transformer lam)))

(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))
(define-syntax (star stx) (raise-syntax-error 'star "Outside regex" stx))

(define-for-syntax (compile-regex e)
  (syntax-parse
   e
   #:literals (seq union star epsilon)
   [(star lhs:expr)
    (with-syntax*
        ([start_star (generate-temporary 'start_star)]
         [(_ (starts_1 ...) ([accepting-state_1 (accepting-rule_1 ...)] ...) (non-accepting_1 ...))
          (compile-regex #'lhs)])
      (quasisyntax/loc e
        (nfa* (start_star) 
              ([start_star ([epsilon (starts_1 ...)])])
              ([accepting-state_1 ([epsilon (start_star)] accepting-rule_1 ...)] ...
               non-accepting_1 ...))))]
   [(seq lhs:expr rhs:expr)
    (with-syntax* 
        ([(_ (starts_1 ...) ([accepting-state_1 (accepting-rule_1 ...)] ...) (non-accepting_1 ...))
          (compile-regex #'lhs)]
         [(_ (starts_2 ...) (accepting_2 ...) (non-accepting_2 ...))
          (compile-regex #'rhs)]
         [([accepting-state_2 . _] ...) #'(accepting_2 ...)])
      (quasisyntax/loc e
        (nfa* (starts_1 ...)
              (accepting_2 ...)
              ([accepting-state_1 ([epsilon (starts_2 ...)] accepting-rule_1 ...)] ...
               non-accepting_1 ...
               non-accepting_2 ...))))]
   [(seq lhs:expr rest:expr ...)
    (compile-regex #'(seq lhs (seq rest ...)))]
   [(union lhs:expr rhs:expr)
    (with-syntax* 
        ([(_ (starts_1 ...) (accepting_1 ...) (non-accepting_1 ...)) (compile-regex #'lhs)]
         [(_ (starts_2 ...) (accepting_2 ...) (non-accepting_2 ...)) (compile-regex #'rhs)])
      (quasisyntax/loc e
        (nfa* (starts_1 ... starts_2 ...)
              (accepting_1 ... accepting_2 ...)
              (non-accepting_1 ... non-accepting_2 ...))))]
   [(union lhs:expr rest:expr ...)
    (compile-regex #'(union lhs (union rest ...)))]
   [(~var transformer (static regex-transformer? "regex transformer"))
    (compile-regex ((regex-transformer->regex (attribute transformer.value)) e))]
   [((~var transformer (static regex-transformer? "regex transformer")) . _)
    (compile-regex ((regex-transformer->regex (attribute transformer.value)) e))]
   [epsilon
    (with-syntax ([start (generate-temporary #'pat)])
      (quasisyntax/loc e
        (nfa* (start) ([start ()]) ())))]
   [pat:expr
    (with-syntax ([start (generate-temporary #'pat)]
                  [end (generate-temporary 'end)])
      (quasisyntax/loc e
        (nfa* (start) ([end ()]) ([start ([pat (end)])]))))]))

(require (for-syntax racket/pretty))
(define-syntax (regex stx)
  (syntax-parse
   stx
   [(_ e:expr)
    (with-syntax*
        ([(_ starts (accepting-rule ...) (non-accepting-rule ...))
          (compile-regex #'e)]
         [([accepting-state . _] ...) #'(accepting-rule ...)])
      (quasisyntax/loc stx
        (nfa/ep starts (accepting-state ...)
                accepting-rule ...
                non-accepting-rule ...)))]))

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
   [x:id #'(plus (and 1 (not 1)))]))
(define-regex-transformer complement
  (λ (stx)
    (raise-syntax-error 'complement "Not supported" stx)))
(define-regex-transformer difference
  (syntax-rules ()
    [(_ A B)
     (intersection A (complement B))]))
(define-regex-transformer intersection
  (syntax-rules ()
    [(_ A B)
     (complement (union (complement A) (complement B)))]))

(provide opt plus rep never difference intersection)

(require tests/eli-tester)

(define-syntax-rule (test-regex* R (succ ...) (fail ...))
  (let ()
    (define r (regex R))
    (test #:failure-prefix (format "~s" 'R)
          (test
           (regex-accepts? r succ) ...
           (not (regex-accepts? r fail)) ...))))
(define-syntax-rule (test-regex R (succ ...) (fail ...))
  (test (test-regex* R (succ ...) (fail ...))
        #;(test-regex* (complement R) (fail ...) (succ ...))))

(test
 (test-regex "A"
             [(list "A")]
             [(list)
              (list "B")])
 
 #;(test-regex (complement "A")
             [(list)
              (list "B")
              (list "A" "A")]
             [(list "A")])
 
 (test-regex (seq 0 1)
             [(list 0 1)]
             [(list)
              (list 0)
              (list 0 1 1)])
 
 (test-regex (union 0 1)
             [(list 1)
              (list 0)]
             [(list)
              (list 0 1)
              (list 0 1 1)])
 
 (test-regex (star 0)
             [(list)
              (list 0)
              (list 0 0)]
             [(list 1)])
 
 (test-regex epsilon
             [(list)]
             [(list 0)])
 
 (test-regex (opt "A")
             [(list)
              (list "A")]
             [(list "B")])

 (test-regex (plus "A")
             [(list "A")
              (list "A" "A")]
             [(list)])
 
 (test-regex (rep "A" 3)
             [(list "A" "A" "A")]
             [(list)
              (list "A")
              (list "A" "A")])
 
 (test-regex never
             []
             [(list) (list 1)])
 
 #;(test-regex (difference (? even?) 2)
             [(list 4)
              (list 6)]
             [(list 3)
              (list 2)])
 
 #;(test-regex (intersection (? even?) 2)
             [(list 2)]
             [(list 1)
              (list 4)])
 
 #;(test-regex (complement (seq "A" (opt "B")))
             [(list "A" "B" "C")]
             [(list "A")
              (list "A" "B")])
 
 (test-regex (seq epsilon
              (union (seq (star 1) (star (seq 0 (star 1) 0 (star 1))))
                     (seq (star 0) (star (seq 1 (star 0) 1 (star 0)))))
              epsilon)
             [(list 1 0 1 0 1)
              (list 0 1 0 1 0)
              (list 1 0 1 1 0 1)
              (list 0 1 0 0 1 0)
              (list)]
             [(list 1 0)]))