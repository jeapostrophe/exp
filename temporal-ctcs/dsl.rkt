#lang racket
(require "automata2/re.rkt"
         "automata2/re-ext.rkt")

(M K (forall (z ...) T))
(K (Pair K K)
   (Sum K K)
   (: n (-> K K))
   ?)
(T (call n p)
   (ret n p)
   dot
   (seq T T)
   (* T)
   (not T)
   (U T T))
(p _
   z
   c)

(define MallocFreeSpec
  (M (Pair (: malloc (-> void? addr?))
           (: free (-> addr? void?)))
     (forall (z)
             (not (seq (call free z)
                       (seq (* (not (ret malloc z)))
                            (call free z)))))))


