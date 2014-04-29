#lang racket/base
(require (for-syntax racket/base
                     "lib.rkt"))

(define-syntax (macro stx)
  (define old (global))
  (global 1)
  #`(printf "static: global was ~a\n" '#,old))

(provide macro)
