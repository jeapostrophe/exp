#lang racket/base
(require racket/contract)

(struct machine (next)
        #:property prop:procedure 0)
(struct machine-accepting machine)

(define (machine-complement m)
  (define const
    (if (machine-accepting? m) machine machine-accepting))
  (const
   (λ (input)
     (machine-complement (m input)))))

(define (machine-union m1 m2)
  (define const
    (if (or (machine-accepting? m1)
            (machine-accepting? m2))
        machine-accepting
        machine))
  (const
   (λ (input)
     (machine-union (m1 input) (m2 input)))))

(define (machine-seq m1 m2)
  ; If they both start accepting, then they both accept the empty string,
  ; so we should accept
  (define initial
    (if (and (machine-accepting? m1) (machine-accepting? m2))
        machine-accepting
        machine))
  (initial
   (λ (input)
     (define finish-m1
       (machine-seq (m1 input) m2))
     (if (machine-accepting? m)
         ; We should either keep going with m1 and then m2 or switch to m2 entirely
         (machine-union finish-m1 m2)
         ; We should keep running m1 until we're done and do m2
         finish-m1))))

(define (machine-star m1)
  (machine-accepting
   (λ (input)
     (machine-seq (m1 input) (machine-start m1)))))

(provide/contract
 [struct-out machine]
 [struct-out machine-accepting]
 [machine-complement (machine? . -> . machine?)]
 [machine-union (machine? machine? . -> . machine?)])