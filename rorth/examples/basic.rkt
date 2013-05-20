#lang racket/base
(require racket/match
         "../main.rkt")
(module+ test
  (require rackunit))

(define/rorth :dup (1 -- 2)
  #:lower stack
  (match-define (list* top rest) stack)
  (list* top top rest))
(define/rorth :drop (1 -- 0)
  #:lower stack
  (match-define (list* top rest) stack)
  rest)
(define/rorth :swap (2 -- 2)
  #:lower stack
  (match-define (list* a b rest) stack)
  (list* b a rest))
(define/rorth :rot (3 -- 3)
  #:lower stack
  (match-define (list* a b c rest) stack)
  (list* c a b rest))
(define/rorth :over (2 -- 3)
  #:lower stack
  (match-define (list* a b rest) stack)
  (list* b a b rest))
(define/rorth :tuck (2 -- 3)
  #:lower stack
  (match-define (list* a b rest) stack)
  (list* a b a rest))
(define/rorth :pick
  #:lower stack
  (match-define (list* i rest) stack)
  (list* (list-ref rest i) rest))

(define/rorth :+ (2 -- 1)
  #:lift +)
(define/rorth :- (2 -- 1)
  #:lift -)
(define/rorth :* (2 -- 1)
  #:lift *)

(module+ test
  (check-equal?
   (rorth 2 -52 :*)
   (list -104))
  (check-equal?
   (rorth 5 57 :-)
   (list -52))
  (check-equal?
   (rorth 2 5 57 :- :*)
   (list -104))
  (check-equal?
   (rorth 73 -16 :+)
   (list 57))
  (check-equal?
   (rorth 2 5 73 -16 :+ :- :*)
   (list -104))

  (check-rorth
   (2 5 73 -16)
   (2 5 73 -16))
  (check-rorth
   (2 5 73 -16 :+)
   (2 5 57))
  (check-rorth
   (2 5 73 -16 :+ :-)
   (2 -52))
  (check-rorth
   (2 5 73 -16 :+ :- :*)
   (-104))

  (check-rorth
   (2 5 73 -16 :drop)
   (2 5 73))
  (check-rorth
   (2 5 73 -16 :swap)
   (2 5 -16 73))
  (check-rorth
   (2 5 73 -16 :rot)
   (2 73 -16 5))
  (check-rorth
   (2 5 73 -16 :dup)
   (2 5 73 -16 -16))
  (check-rorth
   (2 5 73 -16 :over)
   (2 5 73 -16 73))
  (check-rorth
   (2 5 73 -16 :tuck)
   (2 5 -16 73 -16))
  (check-rorth
   (2 5 73 -16 3 :pick)
   (2 5 73 -16 2)))

(define/rorth :sum-of-squares (2 -- 1)
  :dup :* :swap :dup :* :+)

(module+ test
  (check-equal?
   (:sum-of-squares 1 2)
   5)
  (check-rorth
   (1 2 :sum-of-squares)
   (5)))

(define/rorth :squared (1 -- 1)
  :dup :*)

(define/rorth :sum-of-squares2 (2 -- 1)
  :squared :swap :squared :+)

(module+ test
  (check-equal?
   (:sum-of-squares2 1 2)
   5)
  (check-rorth
   (1 2 :sum-of-squares2)
   (5)))

(define (squared2 x)
  (* x x))

(define/rorth :squared2 (1 -- 1)
  #:lift squared2)

(define/rorth :sum-of-squares3 (2 -- 1)
  :squared2 :swap :squared2 :+)

(module+ test
  (check-equal?
   (:sum-of-squares3 1 2)
   5)
  (check-rorth
   (1 2 :sum-of-squares3)
   (5)))

(define (weird x y)
  (values x (* x x) y))

(define/rorth :weird (2 -- 3)
  #:lift weird)

(module+ test
  (check-rorth
   (1 2 :weird)
   (1 1 2)))

(module+ test
  (check-rorth
   (1 2 (rorthda :+ 0 :swap :-))
   (-3)))

(define (make-adder x)
  (rorthda x :+))

(module+ test
  (check-rorth
   (7 (make-adder 5))
   (12)))

(struct :delay (v))

(define/rorth :apply (1 -- 1)
  #:lower stack
  (match-define (list* (:delay thing) rest) stack)
  (rorth #:stack rest thing))

(module+ test
  (check-rorth
   ((:delay (make-adder 5)) :dup 7 :swap :apply :swap :apply)
   (17)))
