#lang racket/load

(module ltl-dsl racket
  (require "ltl.rkt" "temporal.rkt")
  (define (make-ltl-predicate f)
    (make-trace-predicate
     (λ (evts)
       (models (reverse evts) f))))
  (provide make-ltl-predicate))

(module affine-ltl racket
  (require 'ltl-dsl "ltl.rkt" "temporal.rkt")
  (define (get-affine)
    void)
  (define affine-call? 
    (match-lambda 
      [(evt:call 'affine _ _ _ _ _ _) #t]
      [_ #f]))
  (define (make-affine-monitor)
    (make-ltl-predicate
     (ltl:always
      (ltl:-> (ltl:P affine-call?)
              (ltl:X
               (ltl:always
                (ltl:not (ltl:P affine-call?))))))))
  (provide/contract
   [get-affine
    (-> (*->t make-affine-monitor 'affine void))]))

(module affine-ltl-tester racket
  (require 'affine-ltl tests/eli-tester)
  
  (test
   (let ([a (get-affine)])
     (a))
   
   (let ([a (get-affine)])
     (a))
   
   (let ([a (get-affine)])
     (a)
     (a))
   =error>
   "disallow"
   
   (let ([a (get-affine)])
     (a))))

(require 'affine-ltl-tester)