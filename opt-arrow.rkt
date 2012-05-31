#lang typed/racket/base
(require (for-syntax racket/base))

(: foo
   (case-> [Integer Integer -> Integer]
           [Integer Integer Integer -> Integer]
           [Integer Integer Integer Integer -> Integer]))
(define foo
  (opt-lambda: ([w : Integer] [x : Integer] [y : Integer 3] [z : Integer 4])
    (+ w x y z)))

(foo 1 2)
(foo 1 2 3)
(foo 1 2 3 4)

(begin-for-syntax
  (define opt->
    (cons 't-macro
          (λ (stx)
            (printf "inside opt->\n")
            (syntax-case stx (? ->)
              [(_ [req-arg ... (? opt-arg ...) -> ret])
               (syntax/loc stx
                 [req-arg ... opt-arg ... -> ret])])))))

(: foo2
   (opt-> [Integer Integer (? Integer Integer) -> Integer]))
(define foo2
  (opt-lambda: ([w : Integer] [x : Integer] [y : Integer 3] [z : Integer 4])
    (+ w x y z)))

(foo2 1 2)
(foo2 1 2 3)
(foo2 1 2 3 4)
