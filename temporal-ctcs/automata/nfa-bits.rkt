#lang racket/base

; XXX This needs to use machine.rkt

(require "machine.rkt"
         racket/local
         racket/unsafe/ops
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     syntax/id-table
                     unstable/syntax
                     racket/dict
                     racket/list
                     racket/base))

(define-syntax (nfa stx)
  (syntax-parse
   stx
   [(_ (start:id ...)
       (end:id ...)
       [state:id ([evt:expr (next-state:id ...)]
                  ...)]
       ...)
    (define how-many (length (syntax->list #'(state ...))))
    
    (define state->num (make-bound-id-table))
    (for ([state (in-list (syntax->list #'(state ...)))]
          [i (in-range how-many)])
      (dict-set! state->num state i))
    
    (define (set->num sl)
      (for/fold ([end-set 0])
        ([end (in-list (syntax->list sl))])
        (bitwise-ior end-set
                     (arithmetic-shift 1 (dict-ref state->num end)))))
    (define end-set (set->num #'(end ...)))
    (define start-set (set->num #'(start ...)))
    
    (define is-fixnum? (fixnum? how-many))
    
    (with-syntax*
        ([(state_n ...) (build-list how-many (λ (x) x))]
         [end-set end-set]
         [start-set start-set]
         [((next-state_n ...) ...)
          (for/list ([states (in-list (syntax->list #'(((next-state ...) ...) ...)))])
            (syntax-map set->num states))]
         ; Use optimized version if there are not too many states
         [op= (if is-fixnum? #'unsafe-fx= #'=)]
         [bit-shift (if is-fixnum? #'unsafe-fxlshift #'arithmetic-shift)]
         [bit-ior (if is-fixnum? #'unsafe-fxior #'bitwise-ior)]
         [bit-and (if is-fixnum? #'unsafe-fxand #'bitwise-and)])
      (syntax/loc stx
        (local
          [; run : (seteq state) input -> (seteq state)
           (define (run current-states input)
             (define next 0)
             (define compare 1)
             (begin
               (unless (op= 0 (bit-and current-states compare))
                 (match input
                   [evt (set! next (bit-ior next next-state_n))]
                   ...
                   [_ #f]))
               (set! compare (bit-shift compare 1)))
             ...
             next)
           ; accepting? : (seteq state) -> boolean
           (define (accepting? states)
             (not (op= 0 (bit-and states end-set))))
           ; producer : input -> an-nfa-state
           ; make-an-nfa-state : (seteq state) -> an-nfa-state
           (define (make-an-nfa-state next)
             (define constructor
               (if (accepting? next)
                   machine-accepting
                   machine))
             (constructor
              (λ (input)
                (make-an-nfa-state (run next input)))))
           ; initial : an-nfa-state
           (define initial
             (make-an-nfa-state start-set))]
          initial)))]))

(define nfa-accepting? machine-accepting?)
(define (nfa-advance nfa input) (nfa input))
(define nfa-accepts? machine-accepts?)

(provide
 nfa
 nfa-advance
 nfa-accepting?
 nfa-accepts?)

(require tests/eli-tester)
(define M
  (nfa (s1 s3) (s1 s3)
       [s1 ([0 (s2)]
            [1 (s1)])]
       [s2 ([0 (s1)]
            [1 (s2)])]
       [s3 ([0 (s3)]
            [1 (s4)])]
       [s4 ([0 (s4)]
            [1 (s3)])]))

(test
 (nfa-accepts? M (list 1 0 1 0 1))
 (nfa-accepts? M (list 0 1 0 1 0))
 (nfa-accepts? M (list 1 0 1 1 0 1))
 (nfa-accepts? M (list 0 1 0 0 1 0))
 (nfa-accepts? M (list))
 (nfa-accepts? M (list 1 0)) => #f)

