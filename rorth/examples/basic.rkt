#lang racket/base
(require "../main.rkt")
(module+ test
  (require rackunit))

(module+ test
  (check-equal?
   (rorth 2 5 73 -16 + - *)
   -104)
  (check-rorth
   (2 5 73 -16 + - *)
   (-104))

  (check-rorth
   (2 5 73 -16 drop)
   (2 5 73))
  (check-rorth
   (2 5 73 -16 swap)
   (2 5 -16 73))
  (check-rorth
   (2 5 73 -16 rot)
   (2 73 -16 5))
  (check-rorth
   (2 5 73 -16 dup)
   (2 5 73 -16 -16))
  (check-rorth
   (2 5 73 -16 over)
   (2 5 73 -16 73))
  (check-rorth
   (2 5 73 -16 tuck)
   (2 5 73 -16 -16))
  (check-rorth
   (2 5 73 -16 3 pick)
   (2 5 73 -16 2))
  (check-rorth
   (2 5 73 -16 3 roll)
   (5 73 -16 2)))

(define/rorth sum-of-squares (a b -- x)
  dup * swap dup * +)

(module+ test
  (check-equal?
   (sum-of-squares 1 2)
   5)
  (check-rorth
   (1 2 sum-of-squares)
   (5)))

(define/rorth square (a -- x)
  dup *)

(define/rorth sum-of-squares2 (a b -- x)
  squared swap squared +)

(module+ test
  (check-equal?
   (sum-of-squares2 1 2)
   5)
  (check-rorth
   (1 2 sum-of-squares2)
   (5)))

(define (squared2 x)
  (* x x))

(define-rorth squared2 (a -- x)
  :squared2)

(define/rorth sum-of-squares3 (a b -- x)
  squared2 swap squared2 +)

(module+ test
  (check-equal?
   (sum-of-squares3 1 2)
   5)
  (check-rorth
   (1 2 sum-of-squares3)
   (5)))

(define (weird x y)
  (values x (* x x) y))

(define-rorth weird (a b -- x y z)
  :weird)

(module+ test
  (check-rorth
   (1 2 weird)
   (1 1 2)))
