#lang racket/base
(require racket/runtime-path
         ffi/unsafe)
(define-runtime-path lib.so-path "lib.so")
(define lib.so (ffi-lib lib.so-path))
(define global (make-c-parameter "global" lib.so _int))

(provide global)
