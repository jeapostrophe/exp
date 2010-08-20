#lang racket
(require "redex-comp.rkt")

(define-language lang
  [e num
     (+ e e)]
  [E hole
     (+ E e)
     (+ number E)])

#;(define red
  (reduction-relation 
   lang
   #:domain e
   [--> (in-hole E (+ number_0 number_1))
        (in-hole E ,(+ (term number_0) (term number_1)))]))

#;(define (make-term n)
  (if (zero? n)
      1
      (let ([m (make-term (sub1 n))])
        (term lang (+ ,m ,m)))))

#;(define huge-term
  (make-term 10))

#;(time
 (apply-reduction-relation* red huge-term))