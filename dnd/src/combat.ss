#lang scheme
(require "dice.ss")

(define attack-result/c
  (or/c (symbols 'crit) exact-nonnegative-integer?))
(define (attack attack-die)
  (define atk-roll (send attack-die roll))
  (if (= atk-roll (send attack-die max))
      'crit
      atk-roll))

(provide/contract
 [attack-result/c contract?]
 [attack (dice/c . -> . attack-result/c)])

(define damage/c
  (or/c false/c exact-nonnegative-integer?))
(define (attack-vs attack-die damage-die to-hit)
  (define atk-res (attack attack-die))
  (cond
    [(eq? atk-res 'crit)
     (send damage-die crit)]
    [(atk-res . >= . to-hit)
     (send damage-die roll)]
    [else
     #f]))

(provide/contract
 [damage/c contract?]
 [attack-vs (dice/c dice/c exact-nonnegative-integer? . -> . damage/c)])

(define (attack-vs* attack-die damage-die to-hits)
  ; Roll damage once...
  (define one-dmg (send damage-die roll))
  (define damage-die/one
    (new (class* object% (dice<%>)
           (define/public (roll) one-dmg)
           (define/public (max) (send damage-die max))
           ; Roll crits separately
           (define/public (crit) (send damage-die crit))
           (super-new))))
  ; But attack multiple times
  (map (lambda (to-hit)
         (attack-vs attack-die damage-die/one to-hit))
       to-hits))

(provide/contract
 [attack-vs* (dice/c dice/c (listof exact-nonnegative-integer?) . -> . (listof damage/c))])