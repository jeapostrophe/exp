#lang racket/load

(module sort/c racket
  (require "temporal.rkt" "bad-re.rkt")
  (define sort-monitor
    (make-trace-predicate
     (λ (evts)
       (not
        (or 
         ; Are we returning from order after a return from sort, where we previously projected this
         ; order?
         (evt-regexp evts
                     (evt:call 'order proj _ _ _ _ _) _ ...
                     (evt:return 'sort _ _ _ _ _ _ _) _ ...
                     (evt:proj 'order proj _) _ ...)
         ; Is there a witness that the order is not transitive?
         (evt-regexp evts
                     (evt:return 'order _ f _ _ _ (list c b) (list #f)) _ ...
                     (evt:return 'order _ f _ _ _ (list b a) (list #t)) _ ...
                     (evt:return 'order _ f _ _ _ (list c a) (list #f)) _ ...))))))
  (define sort/c
    (->t sort-monitor 'sort
         (->t sort-monitor 'order
              any/c any/c boolean?)
         (listof any/c)
         (listof any/c)))
  (provide sort/c))


(module raw-sort racket
  (define (insert <= e l)
    (cond
      [(empty? l)
       (list e)]
      [(<= e (first l))
       (list* e l)]
      [else
       (list* (first l)
              (insert <= e (rest l)))]))
  (define (sort <= l)
    (if (empty? l)
        empty
        (insert <= (first l)
                (sort <= (rest l)))))
  (provide sort))

(module sort racket
  (require 'sort/c 'raw-sort)
  (provide/contract
   [sort sort/c]))

(module bad-sort racket
  (require 'sort/c (prefix-in raw: 'raw-sort))
  (define last-<= #f)
  (define (sort <= l)
    (define actual-<=
      (if (not last-<=)
          (begin #;(printf "Saving <= for later\n")
                 (set! last-<= <=)
                 <=)
          (begin #;(printf "Using old <=\n")
                 last-<=)))
    (raw:sort actual-<= l))
  (provide/contract
   [sort sort/c]))

(module sort-client racket
  (require tests/eli-tester
           (prefix-in racket: racket/base)
           (prefix-in good: 'sort)
           (prefix-in bad: 'bad-sort))
  (define good:<= <=)
  (define (bad:<= a b)
    (match* 
     (a b)
           ; We should have...
           ; 0 <= 1 <= 2 | b <= a <= c
           ; But by...
     [(1 0) #f] ; 0 <= 1 | a <= b
     [(2 0) #t] ; 2 <= 0 | c <= a
     [(1 2) #f] ; 2 <= 1 | c <= b
     ))
  (define l (build-list 2 (λ (i) (random 10))))
  (define sorted-l (racket:sort l <=))
  (test
   (good:sort good:<= l) => sorted-l
   (good:sort good:<= l) => sorted-l
   
   (bad:sort good:<= l) => sorted-l
   (bad:sort good:<= l) =error> "disallowed"
   
   (good:sort bad:<= (list 1 0)) => (list 0 1)
   (good:sort bad:<= (list 2 0)) => (list 2 0) ; Remember the sort is broken
   (good:sort bad:<= (list 1 2)) =error> "disallowed" ; But now we know
   ))

(require 'sort-client)