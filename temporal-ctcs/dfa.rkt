#lang racket/base
(require racket/local
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     racket/list
                     racket/base))

(struct a-dfa-state (accepting? next))

(define-syntax (dfa stx)
  (syntax-parse
   stx
   [(_ start:id
       (end:id ...)
       [state:id ([evt:expr next-state:id]
                  ...)]
       ...)
    (syntax/loc stx
      (local
        [(define (fail _) fail)
         (define state 
           (match-lambda
             [evt next-state]
             ...
             [_ fail]))
         ...
         ; accepting? : state -> boolean
         (define (accepting? next)
           (or (eq? end next)
               ...))
         ; producer : input -> a-dfa-state
         ; make-a-dfa-state : (seteq state) -> a-dfa-state
         (define (make-a-dfa-state next)
           (a-dfa-state (accepting? next) 
                        (λ (input) (make-a-dfa-state (next input)))))
         (define initial (make-a-dfa-state start))]
        initial))]))

(define dfa-accepting? a-dfa-state-accepting?)
(define (dfa-advance dfa input)
  ((a-dfa-state-next dfa) input))

(define (dfa-accepts? dfa evts)
  (if (empty? evts)
      (dfa-accepting? dfa)
      (dfa-accepts? (dfa-advance dfa (first evts)) (rest evts))))

(provide
 dfa
 dfa-advance
 dfa-accepting?
 dfa-accepts?)

(require tests/eli-tester)
(define M
  (dfa s1 (s1)
       [s1 ([0 s2]
            [1 s1])]
       [s2 ([0 s1]
            [1 s2])]))

(test
 (dfa-accepts? M (list 1 0 1 0 1))
 (dfa-accepts? M (list 1 0 1 1 0 1))
 (dfa-accepts? M (list 0 1 0 0 1 0))
 (dfa-accepts? M (list))
 (dfa-accepts? M (list 1 0)) => #f)

