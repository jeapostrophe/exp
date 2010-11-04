#lang racket/base
(require racket/local
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     racket/list
                     racket/base))

(struct an-nfa/ep-state (accepting? next))

(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside nfa/ep" stx))
(define-syntax (nfa/ep stx)
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
        [(define state 
           (match-lambda
             [evt (seteq next-state ...)]
             ...
             [_ (seteq)]))
         ...
         ; epsilon-states : state -> (seteq state ...)
         (define (epsilon-states st)
           (cond
             [(eq? st state)
              (seteq state epsilon-state ...)]
             ...))
         ; run : (seteq state) input -> (seteq state)
         (define (run current-states input)
           (define next-states
             (for/fold ([next-states (seteq)])
               ([current-state (in-set current-states)])
               (set-union next-states
                          (current-state input))))
           next-states)
         ; accepting? : (seteq state) -> boolean
         (define (accepting? states)
           (for/or ([next (in-set states)])
             (or (eq? end next)
                 ...)))
         ; producer : input -> an-nfa/ep-state
         ; make-an-nfa/ep-state : (seteq state) -> an-nfa/ep-state
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
         (define (make-an-nfa/ep-state current-states)
           (define next (add-epsilon-states* current-states))
           (an-nfa/ep-state (accepting? next)
                         (λ (input)
                           (make-an-nfa/ep-state (run next input)))))
         ; initial : an-nfa/ep-state
         (define initial
           (make-an-nfa/ep-state (seteq start)))]
        initial))]))

(define (nfa/ep-advance nfa/ep input)
  ((an-nfa/ep-state-next nfa/ep) input))

(define (nfa/ep-accepts? nfa/ep evts)
  (if (empty? evts)
      (an-nfa/ep-state-accepting? nfa/ep)
      (nfa/ep-accepts? (nfa/ep-advance nfa/ep (first evts)) (rest evts))))

(provide
 epsilon
 nfa/ep
 nfa/ep-advance
 nfa/ep-accepts?)

(require tests/eli-tester)
(define M
  (nfa/ep s0 (s1 s3)
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

