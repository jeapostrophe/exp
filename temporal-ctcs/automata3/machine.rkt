#lang racket/base
(require racket/contract
         racket/list)

(struct machine (next)
        #:property prop:procedure 0)
(struct machine-accepting machine ())

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

(define (machine-intersect m1 m2)
  (machine-complement
   (machine-union
    (machine-complement m1)
    (machine-complement m2))))

(define (machine-seq* m1 make-m2)
  (define seqd-next
    (λ (input)
      (machine-seq* (m1 input) make-m2)))
  (if (machine-accepting? m1)
      (let ([m2 (make-m2)])
        (machine-union 
         (if (machine-accepting? m2)
             (machine-accepting seqd-next)
             (machine seqd-next))
         m2))
      (machine seqd-next)))

(define (machine-seq m1 m2)
  (machine-seq* m1 (λ () m2)))

(define (machine-star m1)
  (machine-accepting
   (machine-next
    (machine-seq* 
     ; Since seq* will force the RHS if m1 is accepting, this could go into
     ; an infinite loop. However, by removing the accepting-ness, we don't change
     ; the overall behavior because we ultimately make it initially accepting.
     (machine (machine-next m1))
     (λ () (machine-star m1))))))

(define (machine-accepts? m evts)
  (if (empty? evts)
      (machine-accepting? m)
      (machine-accepts? (m (first evts)) (rest evts))))
(define (machine-accepts?/prefix-closed m evts)
  (if (empty? evts)
      (machine-accepting? m)
      (let ([n (m (first evts))])
        (and (machine-accepting? n)
             (machine-accepts? n (rest evts))))))

(define machine-null
  (machine (λ (input) machine-null)))
(define machine-epsilon
  (machine-accepting (λ (input) machine-null)))
(define machine-sigma
  (machine-accepting (λ (input) machine-sigma)))

(provide/contract
 [machine-accepts? (machine? (listof any/c) . -> . boolean?)]
 [machine-accepts?/prefix-closed (machine? (listof any/c) . -> . boolean?)]
 [struct machine ([next (any/c . -> . machine?)])]
 [struct (machine-accepting machine) ([next (any/c . -> . machine?)])]
 [machine-null machine?]
 [machine-epsilon machine?]
 [machine-sigma machine?]
 [machine-complement (machine? . -> . machine?)]
 [machine-union (machine? machine? . -> . machine?)]
 [machine-intersect (machine? machine? . -> . machine?)]
 [machine-seq* (machine? (-> machine?) . -> . machine?)]
 [machine-seq (machine? machine? . -> . machine?)]
 [machine-star (machine? . -> . machine?)])