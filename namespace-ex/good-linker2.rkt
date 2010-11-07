#lang racket
(define f
  (dynamic-require "a.rkt" 'f))
(require "c.rkt")
(go f)