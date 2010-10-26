#lang racket/load

#| This file shows that temporal contracts generalize first and higher order contracts
|#

(module ctcs racket
  (require "temporal.rkt")
  
  (define (f x)
    (add1 x))
  (define (g y)
    "string")
  
  (define (h f)
    (add1 (f 0)))
  (define (i f)
    (f "string"))
  
  (define (monitor b evt)
    (match evt
      ; f : number -> number
      ; g : number -> number
      [(evt:proj (or 'g 'f) _ f)
       f]
      [(evt:call (or 'g 'f) _ _ _ _ _ (list x))
       (if (number? x)
           (list x)
           #f)]
      [(evt:return (or 'g 'f) _ _ _ _ _ _ (list x))
       (if (number? x)
           (list x)
           #f)]
      ; h : (number -> number) -> number
      ; i : (number -> number) -> number
      [(evt:proj (or 'i 'h) _ h) 
       h]
      [(evt:call (or 'i 'h) _ _ _ _ _ (list f))
       (list (((contract-projection (->t* monitor 'f)) (blame-swap b)) f))]
      [(evt:return (or 'i 'h) _ _ _ _ _ _ (list ans))
       (if (number? ans)
           (list ans)
           #f)]))
  
  (provide/contract
   [f (->t* monitor 'f)]
   [g (->t* monitor 'g)]
   [h (->t* monitor 'h)]
   [i (->t* monitor 'i)]))

(module ctcs-test racket
  (require tests/eli-tester
           'ctcs)
  (test
   (f 0) => 1
   (f "str") =error> "disallowed"
   
   (g 0) =error> "disallowed"
   
   (h add1) => 2
   (h (λ (n) "str")) =error> "disallowed"
   
   (i add1) =error> "disallowed"))

(require 'ctcs-test)
