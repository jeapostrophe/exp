#lang racket/base
(require racket/set
         racket/match
         racket/list
         racket/dict
         "dfa.rkt"
         (for-template racket/match))

; XXX Add epsilon

; An NFA is a (nfa (setof state?) (dictof state? (listof (cons pattern (setof state?)))) state? (setof state?)
; where state? must be something equal?-able
;       pattern is a racket/match pattern stx obj
(struct nfa (states transitions start accepting) #:transparent)

(define rule-cross-product
  (match-lambda
    [(list) empty]
    [(list p*ns-l) p*ns-l]
    [(list-rest p*ns-l r)
     (for*/list ([p*ns_0 (in-list p*ns-l)]
                 [p*ns_1 (in-list (rule-cross-product r))])
       (match-define (cons p_0 ns_0) p*ns_0) 
       (match-define (cons p_1 ns_1) p*ns_1)
       (cons #`(and #,p_0 #,p_1)
             (set-union ns_0 ns_1)))]))

(define (set-powerset s)
  (define l (for/list ([e (in-set s)]) e))
  (define list-powerset-list
    (match-lambda
      [(list) 
       (list (set))]
      [(list-rest e l)
       (define lpl (list-powerset-list l))
       ; Keep all the powersets beneath
       (for/fold ([lpl lpl])
         ; And add e to each
         ([ss (in-list lpl)])
         (list* (set-add ss e)
                lpl))]))
  (apply set (list-powerset-list l)))

(define (nfa->dfa n)
  (match-define (nfa Q delta q F) n)
  (define Q_d (set-powerset Q))
  (define q_d (set q))
  (define delta_d
    (for/hash ([R (in-set Q_d)])
      
      (define all-rules
        (for/list ([r (in-set R)])
          (dict-ref delta r)))
      
      (values R (rule-cross-product all-rules))))
  (define F_d
    (for/set ([R (in-set Q_d)]
              #:when (not (set-empty? (set-intersect R F))))
             R))
  (dfa Q_d delta_d q_d F_d))

(nfa->dfa (nfa (set 1 2 3)
               (hash 1 (list (cons #''b (set 2)))
                     2 (list (cons #''a (set 2 3))
                             (cons #''b (set 3)))
                     3 (list (cons #''a (set 1))))
               1
               (set 1)))