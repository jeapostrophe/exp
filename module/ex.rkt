#lang racket/base
(require "module.rkt")

(module og-duck racket/base
  (provide num-eggs quack)
  (define num-eggs 2)
  (define (quack n)
    (unless (zero? n)
      (printf "quack\n")
      (quack (sub1 n)))))
(require (prefix-in og: 'og-duck))
(og:quack og:num-eggs)

(define-module+ duck+
  duck racket/base)
(duck+ (provide num-eggs quack)
       (define num-eggs 2))
(duck+ (define (quack n)
         (unless (zero? n)
           (printf "quack\n")
           (quack (sub1 n)))))

(require 'duck)
(quack num-eggs)

(define nine 9)
(provide nine)

(define-module*+ main+
  main racket/base)
(main+ (require (submod "..")))
(main+ (displayln nine))

(module+ tests
  (printf "Old module+..."))

(module+ tests
  (printf "works!\n"))
