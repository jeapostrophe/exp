#lang racket/load

(module linear racket
  (require "temporal.rkt")
  (define (use-linear f)
    (f void))
  (define linear-monitor
    (make-trace-predicate
     (λ (evts)
       (and
        ; Disallow return from user without call
        (not 
         (evt-regexp evts
                     (evt:return 'user _ _ _ _ app-proj 
                                 (list (app projection-label linear-proj)) _)
                     (not (evt:call 'linear linear-proj _ _ _ _ _)) ...
                     (evt:call 'user _ _ _ _ app-proj _)
                     _ ...))
        ; Disallow two calls
        (not
         (evt-regexp evts
                     (evt:call 'linear proj _ _ _ _ _) _ ...
                     (evt:call 'linear proj _ _ _ _ _) _ ...))))))
  (provide/contract
   [use-linear
    (-> (->t linear-monitor 'user (->t linear-monitor 'linear void) any/c) any/c)]))

(module linear-tester racket
  (require 'linear tests/eli-tester)
  
  (test
   (use-linear
    (λ (a) (a)))
   (use-linear
    (λ (a) (a)))
   
   (use-linear
    (λ (a) (a) (a)))
   =error>
   "disallow"
   
   (use-linear
    (λ (a) (a)))
   
   (use-linear
    (λ (a) (void)))
   =error>
   "disallow"
   
   (use-linear
    (λ (a) 
      (use-linear
       (λ (b) (b)))))
   =error>
   "disallow"
   
   (use-linear
    (λ (a) 
      (use-linear
       (λ (b) (b) (a)))))))

(require 'linear-tester)