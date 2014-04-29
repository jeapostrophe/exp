#lang racket/base
(require racket/runtime-path
         ffi/unsafe)
(define-runtime-path lib.so-path "lib.so")
(define lib.so (ffi-lib lib.so-path))
(define unsafe-global (make-c-parameter "global" lib.so _int))

(define safe-global-box (box 0))
(define safe-global
  (case-lambda
    [() (unbox safe-global-box)]
    [(x) (set-box! safe-global-box x)]))

(provide unsafe-global
         safe-global)
