#lang racket/load

(module affine racket
  (require "temporal.rkt" "bad-re.rkt")
  (define (get-affine)
    void)
  (define affine-monitor
    (make-trace-predicate
     (λ (evts)
       ; Disallow two calls
       (not
        (evt-regexp evts
                    (evt:call 'affine proj _ _ _ _ _) _ ...
                    (evt:call 'affine proj _ _ _ _ _) _ ...)))))
  (provide/contract
   [get-affine
    (-> (->t affine-monitor 'affine void))]))

(module affine-tester racket
  (require 'affine tests/eli-tester)
  
  (test
   (let ([a (get-affine)])
     (void))
   
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

(require 'affine-tester)