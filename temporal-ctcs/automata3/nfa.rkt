#lang racket/base
(require racket/set
         racket/match
         racket/dict
         racket/contract
         racket/function
         "machine.rkt")

(struct nfa (epsilon delta start accepting) #:transparent)

(define (nfa->machine n)
  (match-define (nfa epsilon delta start accepting) n)
  (define E1-cache (make-hash))
  (define (E1 r)
    (if (hash-has-key? E1-cache)
        (hash-ref E1-cache r)
        (begin0 (hash-set! E1-cache r (set))
                (hash-set! E1-cache r (E (dict-ref epsilon r (set)))))))
  (define (E R)
    (for/fold ([R+ (set)]) ([r (in-set R)])
      (set-union R+ (E1 r))))
  (define (state-set->machine R)
    (λ (a)
      (define next
        (for/fold ([next (set)]) ([r (in-set R)])
          (set-union next
                     (E (delta r a)))))
      (values (not (set-empty? (set-intersect next accepting)))
              next)))
  (state-set->machine (E (set start))))

(define state/c any/c)
(define input/c any/c)
(define (set/c elem/c) set?)
(provide/contract
 [struct nfa ([epsilon (hash/c state/c (set/c state/c))]
              [delta (-> state/c input/c (set/c state/c))]
              [start state/c]
              [accepting (set/c state/c)])]
 [nfa->machine (nfa? . -> . accepting-machine/c)])

(define (nfa-seq n1 n2)
  (match-define (nfa e1 d1 s1 a1) n1)
  (match-define (nfa e2 d2 s2 a2) n2)
  ; Keep all the epsilon transitions
  (define e3 (hash-copy e2))
  (for ([(s ss) (in-hash e1)])
    (hash-set! e3 s ss))
  ; But go from all of n1's accepting states to n2's start states
  (for ([s (in-set a1)])
    (hash-update! e3 s (curry set-union s2) (set)))
  ; First ask d1, then d2
  (define (d3 s input)
    (with-handlers ([exn? (λ (x) (d2 s input))])
      (d1 s input)))
  (nfa e3 d3 s1 a2))

(define (nfa-star n1)
  (match-define (nfa e1 d1 s1 a1) n1)
  (define start* (gensym 'start))
  (define a* (set-add a1 start*))
  ; Keep all the epsilon transitions
  (define e* (hash-copy e1))
  ; But go from all of n1's accepting states to the star start
  (for ([s (in-set a*)])
    (hash-update! e* s (curry set-union (set start*) (set))))
  (define (d* s a)
    (if (eq? s start*)
        (set)
        (d1 s a)))
  (nfa e* d* start* a*))
              
(provide/contract
 [nfa-star (nfa? . -> . nfa?)]
 [nfa-seq (nfa? nfa? . -> . nfa?)])