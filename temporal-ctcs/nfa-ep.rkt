#lang racket/base
(require "nfa.rkt"
         (for-syntax syntax/parse
                     unstable/syntax
                     syntax/id-table
                     racket/dict
                     racket/list
                     racket/base))

(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside nfa/ep" stx))
(define-syntax (nfa/ep stx)
  (syntax-parse
   stx
   #:literals (epsilon)
   [(_ (start:id ...)
       (end:id ...)
       [state:id ((~optional [epsilon (epsilon-state:id ...)]
                             #:defaults ([(epsilon-state 1) empty]))
                  [evt:expr (next-state:id ...)]
                  ...)]
       ...)
    (define state->epsilon (make-bound-id-table))
    (for ([stx (in-list (syntax->list #'([state epsilon-state ...] ...)))])
      (syntax-case stx ()
        [[state . es]
         (bound-id-table-set! state->epsilon #'state (syntax->list #'es))]))
    (define seen? (make-parameter (make-immutable-bound-id-table)))
    (define (state->epsilons state)
      (if (dict-has-key? (seen?) state)
          empty
          (parameterize ([seen? (bound-id-table-set (seen?) state #t)])
            (define es (bound-id-table-ref state->epsilon state empty))
            (list* state (append-map state->epsilons es)))))
    (with-syntax*
        ([((start* ...) ...)
          (syntax-map state->epsilons #'(start ...))]
         [((((next-state* ...) ...) ...) ...)
          (syntax-map (λ (ns*)
                        (syntax-map (λ (ns)
                                      (syntax-map state->epsilons ns))
                                    ns*))
                      #'(((next-state ...) ...) ...))])
      (syntax/loc stx
        (nfa (start* ... ...)
             (end ...)
             [state ([evt (next-state* ... ...)]
                     ...)]
             ...)))]))

(define nfa/ep-advance nfa-advance)
(define nfa/ep-accepting? nfa-accepting?)
(define nfa/ep-accepts? nfa-accepts?)

(provide
 epsilon
 nfa/ep
 nfa/ep-advance
 nfa/ep-accepting?
 nfa/ep-accepts?)

(require tests/eli-tester)
(define M
  (nfa/ep (s0) (s1 s3)
       [s0 ([epsilon (s1 s3)])]
       [s1 ([0 (s2)]
            [1 (s1)])]
       [s2 ([0 (s1)]
            [1 (s2)])]
       [s3 ([0 (s3)]
            [1 (s4)])]
       [s4 ([0 (s4)]
            [1 (s3)])]))

(test
 (nfa/ep-accepts? M (list 1 0 1 0 1))
 (nfa/ep-accepts? M (list 0 1 0 1 0))
 (nfa/ep-accepts? M (list 1 0 1 1 0 1))
 (nfa/ep-accepts? M (list 0 1 0 0 1 0))
 (nfa/ep-accepts? M (list))
 (nfa/ep-accepts? M (list 1 0)) => #f)

