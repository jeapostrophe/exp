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

(module qdsl-sort racket
  (require "dsl.rkt" "monitor.rkt" 'raw-sort unstable/match)
  (provide make-sort)
  (define (make-sort)
    (contract
     (with-monitor (label 'sort (-> (label 'order (-> any/c any/c boolean?))
                                    (listof any/c)
                                    (listof any/c)))
       (complement
        (seq (star _) 
             (dseq
              (evt:proj 'order proj _)
              (seq (star _)
                   (evt:return 'sort _ _ _ _ _) (star _)
                   (evt:call 'order (== proj) _ _ _))))))
     sort 'pos 'neg)))

(module dsl-sort racket
  (require "dsl.rkt" "monitor.rkt" 'raw-sort)
  (provide make-sort)
  (define (make-sort)
    (contract (with-monitor (label 'sort (-> (label 'order (-> any/c any/c boolean?))
                                             (listof any/c)
                                             (listof any/c)))
                (complement
                 (seq (star _)
                      (evt:proj 'order _ _) (star _)
                      (evt:return 'sort _ _ _ _ _) (star _)
                      (evt:call 'order _  _ _ _))))
              sort
              'pos 'neg)))

(module smart-sort racket
  (require "monitor.rkt" 'raw-sort)
  (define returned? #f)
  (define (sort-monitor evt)
    (match evt
      [(evt:proj 'order proj _)
       #t]
      [(evt:return 'sort _ _ _ (list f _) _)
       (set! returned? #t)]
      [(evt:call 'order proj _ _ _)
       (not returned?)]
      [_ #t]))
  (provide/contract
   [sort (monitor/c sort-monitor 'sort
                    (-> (monitor/c sort-monitor 'order (-> any/c any/c boolean?))
                        (listof any/c)
                        (listof any/c)))]))

(module sort-timer racket
  (require (prefix-in dsl: 'dsl-sort)
           (prefix-in qdsl: 'qdsl-sort)
           (prefix-in smart: 'smart-sort)
           (prefix-in raw: 'raw-sort)
           (prefix-in ctc: 'ctc-sort)
           tests/stress)
  
  (define l (build-list 200 (compose random add1)))
  (stress 1
          ["raw" (raw:sort <= l)]
          ["ctc" (ctc:sort <= l)]
          ["qdsl" ((qdsl:make-sort) <= l)]
          ["dsl" ((dsl:make-sort) <= l)]
          ["smart" (smart:sort <= l)]))

(require 'sort-timer)