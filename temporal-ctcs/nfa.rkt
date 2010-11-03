#lang racket/base
(require racket/local
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     racket/list
                     racket/base))

(struct an-nfa-state (accepting? next))

(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside nfa" stx))
(define-syntax (nfa stx)
  (syntax-parse
   stx
   #:literals (epsilon)
   [(_ start:id
       (end:id ...)
       [state:id ((~optional [epsilon (epsilon-state:id ...)]
                             #:defaults ([(epsilon-state 1) empty]))
                  [evt:expr (next-state:id ...)]
                  ...)]
       ...)
    (syntax/loc stx
      (local
        [; next : state input -> (seteq state ...)
         (define (next st i)
           (set-union
            (seteq)
            (if (eq? st 'state)
                (match i
                  [evt (seteq 'next-state ...)]
                  ...
                  [_ (seteq)])
                (seteq))
            ...))
         ; epsilon-states : state -> (seteq state ...)
         (define (epsilon-states st)
           (set-union
            (seteq)
            (if (eq? st 'state) (seteq 'state 'epsilon-state ...) (seteq))
            ...))
         ; run : (seteq state) input -> (seteq state)
         (define (run current-states input)
           (define next-states
             (for/fold ([next-states (seteq)])
               ([current-state (in-set current-states)])
               (set-union next-states
                          (next current-state input))))
           next-states)
         ; accepting? : (seteq state) -> boolean
         (define (accepting? states)
           (for/or ([next (in-set states)])
             (or (eq? 'end next)
                 ...)))
         ; producer : input -> an-nfa-state
         ; make-an-nfa-state : (seteq state) -> an-nfa-state
         (define (add-epsilon-states sts)
           (for/fold ([next-states (seteq)])
             ([current-state (in-set sts)])
             (set-union next-states
                        (epsilon-states current-state))))
         (define (add-epsilon-states* sts)
           (define ns (add-epsilon-states sts))
           (if (= (set-count sts) (set-count ns))
               ns
               (add-epsilon-states* ns)))
         (define (make-an-nfa-state current-states)
           (define next (add-epsilon-states* current-states))
           (an-nfa-state (accepting? next)
                         (λ (input)
                           (make-an-nfa-state (run next input)))))
         ; initial : an-nfa-state
         (define initial
           (make-an-nfa-state (seteq 'start)))]
        initial))]))

(define (nfa-advance nfa input)
  ((an-nfa-state-next nfa) input))

(define (nfa-accepts? nfa evts)
  (if (empty? evts)
      (an-nfa-state-accepting? nfa)
      (nfa-accepts? (nfa-advance nfa (first evts)) (rest evts))))

(provide
 epsilon
 nfa
 nfa-advance
 nfa-accepts?)

(require tests/eli-tester)
(define M
  (nfa s0 (s1 s3)
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
 (nfa-accepts? M (list 1 0 1 0 1))
 (nfa-accepts? M (list 0 1 0 1 0))
 (nfa-accepts? M (list 1 0 1 1 0 1))
 (nfa-accepts? M (list 0 1 0 0 1 0))
 (nfa-accepts? M (list))
 (nfa-accepts? M (list 1 0)) => #f)

