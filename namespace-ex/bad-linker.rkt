#lang racket
(define f
  (parameterize ([current-namespace (make-base-namespace)])
    (dynamic-require "a.rkt" 'f)))
(require "c.rkt")
(go f)