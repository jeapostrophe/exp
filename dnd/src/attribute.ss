#lang scheme

(define (attribute-modifier val)
  (floor (/ (- val 10) 2)))

(define attribute-set<%>
  (interface ()))

(define attribute-set/c
  (object-contract
   (field str exact-nonnegative-integer?)
   (field con exact-nonnegative-integer?)
   (field dex exact-nonnegative-integer?)
   (field int exact-nonnegative-integer?)
   (field wis exact-nonnegative-integer?)
   (field cha exact-nonnegative-integer?)))

(define attribute-set%
  (class* object% (attribute-set<%>)
    (init-field str con dex int wis cha)
    (super-new)))

(define-syntax default-as
  (syntax-rules ()
    [(_ min a2 a3 a4 a5 a6)
     (new attribute-set%
          [min 8] [a2 10]
          [a3 10] [a4 10]
          [a5 10] [a6 10])]))

(define default-attribute-set/str
  (default-as str con dex int wis cha))
(define default-attribute-set/con
  (default-as con str dex int wis cha))
(define default-attribute-set/dex
  (default-as dex str con int wis cha))
(define default-attribute-set/int
  (default-as int str con dex wis cha))
(define default-attribute-set/wis
  (default-as wis str con dex int cha))
(define default-attribute-set/cha
  (default-as cha str con dex int wis))