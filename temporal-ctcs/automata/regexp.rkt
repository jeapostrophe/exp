#lang racket
(require "dfa.rkt"
         "regexp-help.rkt"
         (for-syntax syntax/parse
                     racket/list
                     racket/match
                     "regexp-help.rkt"
                     unstable/syntax))

(define-syntax-rule (define-regex-transformer id lam)
  (define-syntax id (regex-transformer lam)))

(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside regex" stx))
(define-syntax (complement stx) (raise-syntax-error 'complement "Outside regex" stx))
(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))
(define-syntax (star stx) (raise-syntax-error 'star "Outside regex" stx))

(define-for-syntax (compile-regex e)
  (syntax-parse
   e
   #:literals (complement seq union star epsilon)
   [(complement lhs:expr)
    #;(with-syntax*
        [(_ start_1 ([accepting-state_1 (accepting-rule_1 ...)] ...) (non-accepting_1 ...))
         (compile-regex #'lhs)]
      ...)
    
    (raise-syntax-error 'regex "Complement not supported" e)]
   [(star lhs:expr)
    (raise-syntax-error 'regex "Star not supported" e)
    #;(with-syntax*
        ([start_star (generate-temporary 'start_star)]
         [(_ (starts_1 ...) ([accepting-state_1 (accepting-rule_1 ...)] ...) (non-accepting_1 ...))
          (compile-regex #'lhs)])
      (quasisyntax/loc e
        (nfa* (start_star) 
              ([start_star ([epsilon (starts_1 ...)])])
              ([accepting-state_1 ([epsilon (start_star)] accepting-rule_1 ...)] ...
               non-accepting_1 ...))))]
   [(seq lhs:expr rhs:expr)
    (raise-syntax-error 'regex "Seq not supported" e)
    #;(with-syntax* 
        ([(_ start_1 ([accepting-state_1 (accepting-rule_1 ...)] ...) (non-accepting_1 ...))
          (compile-regex #'lhs)]
         [(_ start_2 (accepting_2 ...) (non-accepting_2 ...))
          (compile-regex #'rhs)]
         [([accepting-state_2 . _] ...) #'(accepting_2 ...)])
      (quasisyntax/loc e
        (dfa start_1
              (accepting_2 ...)
              ([accepting-state_1 ([epsilon (starts_2 ...)] accepting-rule_1 ...)] ...
               non-accepting_1 ...
               non-accepting_2 ...))))]
   [(seq lhs:expr rest:expr ...)
    (compile-regex #'(seq lhs (seq rest ...)))]
   [(union lhs:expr rhs:expr)
    (define (state-cross-product lhs rhs)
      (for*/list ([a_1 (in-list (syntax->list lhs))]
                  [a_2 (in-list (syntax->list rhs))])
        (with-syntax*
            ([[accept_1 ([evt_1 next_1] ...)] a_1]
             [[accept_2 ([evt_2 next_2] ...)] a_2])
          (quasisyntax
           [a_1*a_2 
           #,@(for*/list ([e_1 (in-list (syntax->list #'([evt_1 next_1] ...)))]
                          [e_2 (in-list (syntax->list #'([evt_2 next_2] ...)))])
                (with-syntax*
                    ([[evt_1 next_1] e_1]
                     [[evt_2 next_2] e_2])
                  (syntax
                   [(and evt_1 evt_2) (
            
            ([evt_1*evt_2 next_1*next_2] ...)]))))
    (with-syntax*
        ([(_ start_1 
             ([accept_1 ([evt_1 next_1] ...)] ...)
             ([!accept_1 ([!evt_1 !next_1] ...)] ...))
          (compile-regex #'lhs)]
         [(_ start_2
             ([accept_2 ([evt_2 next_2] ...)] ...)
             ([!accept_2 ([!evt_2 !next_2] ...)] ...))
          (compile-regex #'lhs)]
         [([accept_1*accept_2 ([evt_1*evt_2 next_1*next_2] ...)])
          (state-cross-product #'([accept_1 ([evt_1 next_1] ...)] ...)
                               #'([accept_2 ([evt_2 next_2] ...)] ...))])
      (dfa start_1*start_2
           ([accept_1*accept_2 ([evt_1*evt_2 next_1*next_2] ...)] ...
            [accept_1*!accept_2 ([evt_1*!evt_2 next_1*!next_2] ...)] ...
            [!accept_1*accept_2 ([!evt_1*evt_2 !next_1*next_2] ...)] ...)
           ([!accept_1*!accept_2 ([!evt_1*!evt_2 !next_1*!next_2] ...)] ...)))
      
    
    (raise-syntax-error 'regex "Union not supported" e)
    #;(with-syntax* 
        ([(_ start_1 (accepting_1 ...) (non-accepting_1 ...)) (compile-regex #'lhs)]
         [(_ start_2 (accepting_2 ...) (non-accepting_2 ...)) (compile-regex #'rhs)])
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
    (syntax/loc e
      (dfa start ([start ()]) ()))]
   [pat:expr
    (syntax/loc e
      (dfa start ([end ()]) ([start ([pat end])])))]))

(define-syntax (regex stx)
  (syntax-case stx ()
    [(_ e)
     (compile-regex #'e)]))

(define regex-accepting? dfa-accepting?)
(define regex-accepts? dfa-accepts?)

(provide
 complement seq union star epsilon
 define-regex-transformer
 regex
 (rename-out [dfa? regex?])
 regex-accepting?
 regex-accepts?)