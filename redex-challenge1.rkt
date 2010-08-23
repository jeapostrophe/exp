#lang racket/load

(module redex racket
  (require redex
           tests/eli-tester)
  
  (define-language L
    (L (+ L L)
       (- L L)
       number)
    (M (+ M M)
       (* M M)
       number)
    (N (+ N N)
       (- N N)
       (* N N)
       number))
  
  (define red
    (reduction-relation
     L #:domain N
     (--> L 1)
     (--> M 2)))
  
  (time
   (test
    (apply-reduction-relation red (term (+ 1 2))) =>
    (list 2 1)
    
    (apply-reduction-relation red (term 3)) =>
    (list 2 1)
    
    (apply-reduction-relation red (term (* 1 2))) =>
    (list 2)
    
    (apply-reduction-relation red (term (- 1 2))) =>
    (list 1))))

(require 'redex)
(collect-garbage) (collect-garbage)

(module jay racket
  (require tests/eli-tester)
  
  (struct L:se ())
  (struct L:+ L:se (se0 se1))
  (struct L:- L:se (se0 se1))
  (struct L:* L:se (se0 se1))
  (struct L:num L:se (n))
  
  (define-syntax-rule (term d) (->L:se 'd))
  
  (define ->L:se
    (match-lambda
      [`(+ ,se0 ,se1)
       (L:+ (->L:se se0) (->L:se se1))]
      [`(- ,se0 ,se1)
       (L:- (->L:se se0) (->L:se se1))]
      [`(* ,se0 ,se1)
       (L:* (->L:se se0) (->L:se se1))]
      [(? number? n)
       (L:num n)]))
  
  (define is-L:L?
    (match-lambda
      [(L:+ e0 e1)
       (and (is-L:L? e0) (is-L:L? e1))]
      [(L:- e0 e1)
       (and (is-L:L? e0) (is-L:L? e1))]
      [(and se (L:num n))
       #t]
      [_
       #f]))
  
  (define is-L:M?
    (match-lambda
      [(L:+ e0 e1)
       (and (is-L:M? e0) (is-L:M? e1))]
      [(L:* e0 e1)
       (and (is-L:M? e0) (is-L:M? e1))]
      [(and se (L:num n))
       #t]
      [_
       #f]))
  
  (define (apply-reduction-relation t)
    (append
     (if (is-L:M? t)
         (list 2)
         empty)
     (if (is-L:L? t)
         (list 1)
         empty)))
  
  (time
   (test
    (apply-reduction-relation (term (+ 1 2))) =>
    (list 2 1)
    
    (apply-reduction-relation (term 3)) =>
    (list 2 1)
    
    (apply-reduction-relation (term (* 1 2))) =>
    (list 2)
    
    (apply-reduction-relation (term (- 1 2))) =>
    (list 1))))

(require 'jay)