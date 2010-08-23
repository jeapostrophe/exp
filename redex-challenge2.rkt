#lang racket/load

(module redex racket
  (require redex
           tests/eli-tester)
  
  (define-language mt
    [t (number ...)])
  
  (define red
    (reduction-relation
     mt #:domain t
     (--> (number_1 ... number_i number_i+1 ...)
          (number_i))))
  
  (time
   (test (apply-reduction-relation
          red                                   
          (term (1 2 3 4 5 6 7)))
         =>
         (list
          (term (1))
          (term (2))
          (term (3))
          (term (4))
          (term (5))
          (term (6))
          (term (7))))))

(require 'redex)
(collect-garbage) (collect-garbage)

(module jay racket
  (require tests/eli-tester)
  
  (struct mt:t (ns) #:transparent)
  
  (define-syntax-rule (term d) (->mt:t 'd))
  
  (define ->mt:t
    (match-lambda
      [(list (? number? n) ...)
       (mt:t n)]))
  
  (define apply-reduction-relation
    (match-lambda
      [(mt:t n)
       (map (compose mt:t list) n)]))
  
  (time
   (test (apply-reduction-relation
          (term (1 2 3 4 5 6 7)))
         =>
         (list
          (term (1))
          (term (2))
          (term (3))
          (term (4))
          (term (5))
          (term (6))
          (term (7))))))

(require 'jay)