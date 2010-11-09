#lang racket
(require "dsl.rkt"
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
  (M (cons/c (n-> malloc addr?)
             (n-> free addr? void?))
     (forall ()
             (complement (seq (star _) (call free _) (star _))))))
(test (test-spec NoFreeSpec) =error> "disallowed")

(define NoFreeTwiceSpec
  (M (cons/c (n-> malloc addr?)
             (n-> free addr? void?))
     (forall ()
             (complement (seq (star _) (call free _) (star _) (call free _) (star _))))))
(test
 ; The whole sequence is rejected
 (re-accepts? (re (complement (seq (star _) 'cf (star _) 'cf (star _))))
              '(cm rm cf rf cm rm cf rf cf rf))
 => #f
 ; The shortest erroring prefix is rejected
 (re-accepts? (re (complement (seq (star _) 'cf (star _) 'cf (star _))))
              '(cm rm cf rf cm rm cf))
 => #f
 (test-spec NoFreeTwiceSpec) =error> "disallowed")

(define MallocFreeSpec
  (M (cons/c (n-> malloc addr?)
             (n-> free addr? void?))
     (forall ()
             (complement (seq (call free _) (star _)
                              (star (complement (ret malloc _)))
                              (call free _)
                              (star _))))))
(test-spec MallocFreeSpec)