#lang racket
(require "dsl.rkt"
         "temporal.rkt"
         tests/eli-tester)

#;(define MallocFreeSpec
    (M (Pair (: malloc (-> void? addr?))
             (: free (-> addr? void?)))
       (forall (z)
               (not (seq (call free z)
                         (seq (* (not (ret malloc z)))
                              (call free z)))))))
(define (test-spec spec)
  (define MallocFreeImpl
    (cons (λ () 0)
          (λ (a) (void))))
  (define MallocFreeProt
    (contract spec MallocFreeImpl
              'pos 'neg))
  
  (match-define (cons malloc free) MallocFreeProt)
  (malloc)
  (free 0)
  (malloc)
  (free 0)
  (free 0))

(define addr? number?)

(define NoFreeSpec
  (M (cons/c (n-> 'malloc addr?)
             (n-> 'free addr? void?))
     (forall ()
             ; It is okay as long as you never call free
             (complement (seq (star _) (call 'free _) (star _))))))
(test (test-spec NoFreeSpec) =error> "disallowed")

(define NoFreeTwiceSpec
  (M (cons/c (n-> 'malloc addr?)
             (n-> 'free addr? void?))
     (forall ()
             (complement (seq (star _) (call 'free _) (star _) (call 'free _) (star _))))))
(test (test-spec NoFreeTwiceSpec) =error> "disallowed")

(define MallocFreeBalancedSpec
  (M (cons/c (n-> 'malloc addr?)
             (n-> 'free addr? void?))
     (forall ()
             (star (seq (call 'malloc)
                        (ret 'malloc _)
                        (call 'free _)
                        (ret 'free _))))))
(test (test-spec MallocFreeBalancedSpec) =error> "disallowed")

; This is a faulty spec because the complement of (ret malloc _) contains a lot
(define MallocFreeSpec
  (M (cons/c (n-> 'malloc addr?)
             (n-> 'free addr? void?))
     (forall ()
             (complement (seq (call 'free _)
                              (star (not (ret 'malloc _)))
                              (call 'free _)
                              (star _))))))
(test (test-spec MallocFreeSpec) =error> "disallowed")

