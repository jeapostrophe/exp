#lang racket
(require "dsl.rkt")

#;(define MallocFreeSpec
    (M (Pair (: malloc (-> void? addr?))
             (: free (-> addr? void?)))
       (forall (z)
               (not (seq (call free z)
                         (seq (* (not (ret malloc z)))
                              (call free z)))))))

(define addr? number?)
(define MallocFreeSpec
  (M (cons/c (n-> malloc addr?)
             (n-> free addr? void?))
     (forall ()
             (complement (seq (call free _) (star _)
                              (star (complement (ret malloc _)))
                              (call free _)
                              (star _))))))

(define MallocFreeImpl
  (cons (λ () 0)
        (λ (a) (void))))

(define MallocFreeProt
  (contract MallocFreeSpec MallocFreeImpl
            'pos 'neg))

(match-define (cons malloc free) MallocFreeProt)
(malloc)
(free 0)
(free 0)
(malloc)
