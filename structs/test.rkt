#lang racket/base

;; Prefab struct
(struct ps (x y) #:prefab)
(test 'prefab-struct ps ps-x ps-y)

;; Struct
(struct s (x y))
(test 'struct s s-x s-y)

;; Unsafe struct
(begin-encourage-inline
  (define (us-x u) (unsafe-struct-ref u 0))
  (define (us-y u) (unsafe-struct-ref u 1)))
(test 'unsafe-struct s us-x us-y)

;; Unsafe struct*
(begin-encourage-inline
  (define (us*-x u) (unsafe-struct*-ref u 0))
  (define (us*-y u) (unsafe-struct*-ref u 1)))
(test 'unsafe-struct* s us*-x us*-y)

;; Vector
(begin-encourage-inline
  (define (v x y) (vector x y))
  (define (v-x u) (vector-ref u 0))
  (define (v-y u) (vector-ref u 1)))
(test 'vector v v-x v-y)

;; Unsafe vector
(begin-encourage-inline
  (define (uv-x u) (unsafe-vector-ref u 0))
  (define (uv-y u) (unsafe-vector-ref u 1)))
(test 'unsafe-vector v uv-x uv-y)

;; Unsafe vector*
(begin-encourage-inline
  (define (uv*-x u) (unsafe-vector*-ref u 0))
  (define (uv*-y u) (unsafe-vector*-ref u 1)))
(test 'unsafe-vector* v uv*-x uv*-y)

;; Flvector
(begin-encourage-inline
  (define (fv x y) (flvector x y))
  (define (fv-x f) (flvector-ref f 0))
  (define (fv-y f) (flvector-ref f 1)))
(test 'flvector fv fv-x fv-y)

;; Unsafe flvector
(begin-encourage-inline
  (define (ufv-x f) (unsafe-flvector-ref f 0))
  (define (ufv-y f) (unsafe-flvector-ref f 1)))
(test 'unsafe-flvector fv ufv-x ufv-y)

;; Cstruct
;; Unsafe cstruct
;; Ptr
;; Unsafe ptr
;; Call out to C individually
;; Call out to C for whole test
