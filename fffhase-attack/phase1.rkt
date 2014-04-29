#lang racket/base
(require (for-syntax racket/base
                     "lib.rkt"))

(define-syntax (macro stx)
  (define unsafe-old (unsafe-global))
  (define safe-old (safe-global))
  (safe-global 1)
  (unsafe-global 1)
  #`(begin 
      (printf "static: unsafe-global was ~a\n" '#,unsafe-old)
      (printf "static: safe-global was ~a\n" '#,safe-old)))

(provide macro)
