#lang racket/base
(require racket/set
         racket/match
         racket/dict
         (for-template racket/match))

(provide
 (struct-out dfa)
 dfa-complement
 dfa-union)

; A DFA is a (dfa (setof state?) (dictof state? (listof (cons pattern state?))) state? (setof state?)
; where state? must be something equal?-able
;       pattern is a racket/match pattern stx obj
(struct dfa (states transitions start accepting) #:transparent)

(define (dfa-complement d)
  (struct-copy dfa d
               [accepting 
                (set-subtract (dfa-states d) (dfa-accepting d))]))

(define (dfa-union lhs rhs)
  (match-define (dfa Q_0 delta_0 q_0 F_0) lhs)
  (match-define (dfa Q_1 delta_1 q_1 F_1) rhs)
  (define Q_u
    (for*/set ([s0 (in-set Q_0)]
               [s1 (in-set Q_1)])
              (cons s0 s1)))
  (define delta_u
    (for/hash ([su (in-set Q_u)])
      (match-define (cons s0 s1) su)
      (values su
              (for*/list ([r0 (in-list (dict-ref delta_0 s0))]
                          [r1 (in-list (dict-ref delta_1 s1))])
                (match-define (cons pat0 next0) r0)
                (match-define (cons pat1 next1) r1)
                (cons #`(and #,pat0 #,pat1)
                      (cons next0 next1))))))
  (define q_u
    (cons q_0 q_1))
  (define F_u
    (for/set ([su (in-set Q_u)]
              #:when (or (set-member? F_0 (car su))
                         (set-member? F_1 (cdr su))))
             su))
  (dfa Q_u delta_u q_u F_u))

; XXX
(define fig1.5
  (dfa (set 'q1 'q2 'q3)
       (hash 'q1 (list (cons #'0 'q1)
                       (cons #'1 'q2))
             'q2 (list (cons #'1 'q2)
                       (cons #'0 'q3))
             'q3 (list (cons #'(or 0 1) 'q2)))
       'q1
       (set 'q2)))
(dfa-complement fig1.5)
(dfa-union fig1.5 fig1.5)