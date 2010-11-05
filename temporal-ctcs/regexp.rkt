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