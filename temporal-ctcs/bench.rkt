#lang racket/load

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

(module ctc-sort racket
  (require 'raw-sort)
  (provide/contract
   [sort (-> (-> any/c any/c boolean?)
             (listof any/c)
             (listof any/c))]))

(module dumb-sort racket
  (require "temporal.rkt" 'raw-sort)
  (define sort-monitor
    (make-trace-predicate
     (λ (evts)
       (not
        (evt-regexp evts
                    (evt:call 'order proj _ _ _ _ _) _ ...
                    (evt:return 'sort _ _ _ _ _ _ _) _ ...
                    (evt:proj 'order proj _) _ ...)))))
  (provide/contract
   [sort (->t sort-monitor 'sort
              (->t sort-monitor 'order
                   any/c any/c boolean?)
              (listof any/c)
              (listof any/c))]))

(module smart-sort racket
  (require "temporal.rkt" 'raw-sort)
  (define returned? (make-weak-hasheq))
  (define (sort-monitor evt)
    (match evt
      [(evt:proj 'order proj _)
       (hash-set! returned? proj #f)]
      [(evt:return 'sort _ _ _ _ _ (list f _) _)
       (hash-set! returned? (projection-label f) #t)]
      [(evt:call 'order proj _ _ _ _ _)
       (not (hash-ref returned? proj #t))]
      [_ #t]))
  (provide/contract
   [sort (->t sort-monitor 'sort
              (->t sort-monitor 'order
                   any/c any/c boolean?)
              (listof any/c)
              (listof any/c))]))

(module sort-timer racket
  (require (prefix-in dumb: 'dumb-sort)
           (prefix-in smart: 'smart-sort)
           (prefix-in raw: 'raw-sort)
           (prefix-in ctc: 'ctc-sort)
           tests/stress)
  
  (define l (build-list 200 (compose random add1)))
  (stress 4
          ["raw" (raw:sort <= l)]
          ["ctc" (ctc:sort <= l)]
          ["dumb" (dumb:sort <= l)]
          ["smart" (smart:sort <= l)]))

(require 'sort-timer)