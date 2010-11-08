#lang racket/base
(require racket/contract
         racket/list)

(struct machine (next)
        #:transparent
        #:property prop:procedure 0)
(struct machine-accepting machine ()
        #:transparent)

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
  (define seqd
    (initial
     (λ (input)
       (machine-seq (m1 input) m2))))
  (if (machine-accepting? m1)
      (machine-union seqd m2)
      seqd))

(define (machine-star m1)
  ; Accept an empty sequence
  (machine-accepting
   (λ (input)
     (define next-m1
        (m1 input))
     (define m2
       (machine-star m1))
     (define finish-m1
       (machine-seq next-m1 m2))
     (if (machine-accepting? next-m1)
         ; If we have reached the end, then potentially stop
         (machine-union finish-m1 m2)
         finish-m1))))

(define (machine-accepts? m evts)
  (if (empty? evts)
      (machine-accepting? m)
      (machine-accepts? (m (first evts)) (rest evts))))

(define machine-null
  (machine (λ (input) machine-null)))
(define machine-epsilon
  (machine-accepting (λ (input) machine-null)))

(provide/contract
 [machine-accepts? (machine? (listof any/c) . -> . boolean?)]
 [struct machine ([next (any/c . -> . machine?)])]
 [struct (machine-accepting machine) ([next (any/c . -> . machine?)])]
 [machine-null machine?]
 [machine-epsilon machine?]
 [machine-complement (machine? . -> . machine?)]
 [machine-union (machine? machine? . -> . machine?)]
 [machine-seq (machine? machine? . -> . machine?)]
 [machine-star (machine? . -> . machine?)])