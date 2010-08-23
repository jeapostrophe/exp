#lang racket/load

(module redex racket
  (require redex/reduction-semantics
           tests/eli-tester)
  
  (define-language mt
    [t (number ...)])
  
  (define red
    (reduction-relation
     mt #:domain t
     (--> (number_1 ...
           number_2 
           number_3 ...
           number_4 
           number_5 ...)
          (number_2 number_4))))
  
  (time
   (test
    (apply-reduction-relation red (term (1 2 3)))
    =>
    (list (term (1 2))
          (term (1 3))
          (term (2 3))))))

(require 'redex)
(collect-garbage) (collect-garbage)

(module jay racket
  (require racket/generator
           tests/eli-tester)
  
  (struct mt:t (ns) #:transparent)
  
  (define-syntax-rule (term d) (->mt:t 'd))
  
  (define ->mt:t
    (match-lambda
      [(list (? number? n) ...)
       (mt:t n)]))
  
  (define apply-reduction-relation
    (match-lambda
      [(mt:t n)
       (for*/list ([n2*after2
                    (in-generator 
                     (let loop ([n n])
                       (unless (empty? n)
                         (yield n)
                         (loop (cdr n)))))]
                   [n4*after4
                    (in-generator 
                     (let loop ([n (cdr n2*after2)])
                       (unless (empty? n)
                         (yield n)
                         (loop (cdr n)))))])
         (mt:t (list (car n2*after2) (car n4*after4))))]))
  
  (time
   (test
    (apply-reduction-relation (term (1 2 3)))
    =>
    (list (term (1 2))
          (term (1 3))
          (term (2 3))))))

(require 'jay)