#lang racket
(require tests/eli-tester
         racket/runtime-path)

(define-runtime-path here ".")

(test
 (for ([f (in-directory here)]
       #:when (regexp-match #rx"ex-.+\\.rkt$" f))
   (test #:failure-prefix f
         (dynamic-require f #f))))