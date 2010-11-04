#lang racket/base
(require racket/local
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     syntax/id-table
                     unstable/syntax
                     racket/dict
                     racket/list
                     racket/base))

(struct an-nfa-state (accepting? next))

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
    
    (with-syntax*
        ([(state_n ...) (build-list how-many (λ (x) x))]
         [end-set end-set]
         [start-set start-set]
         [((next-state_n ...) ...)
          (for/list ([states (in-list (syntax->list #'(((next-state ...) ...) ...)))])
            (syntax-map set->num states))])
      (syntax/loc stx
        (local
          [; run : (seteq state) input -> (seteq state)
           (define (run current-states input)
             (bitwise-ior
              (if (bitwise-bit-set? current-states state_n)
                  (match input
                    [evt next-state_n]
                    ...
                    [_ 0])
                  0)
              ...))
           ; accepting? : (seteq state) -> boolean
           (define (accepting? states)
             (not (zero? (bitwise-and states end-set))))
           ; producer : input -> an-nfa-state
           ; make-an-nfa-state : (seteq state) -> an-nfa-state
           (define (make-an-nfa-state next)
             (an-nfa-state (accepting? next)
                           (λ (input)
                             (make-an-nfa-state (run next input)))))
           ; initial : an-nfa-state
           (define initial
             (make-an-nfa-state start-set))]
          initial)))]))

(define nfa-accepting? an-nfa-state-accepting?)
(define (nfa-advance nfa input)
  ((an-nfa-state-next nfa) input))

(define (nfa-accepts? nfa evts)
  (if (empty? evts)
      (nfa-accepting? nfa)
      (nfa-accepts? (nfa-advance nfa (first evts)) (rest evts))))

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

