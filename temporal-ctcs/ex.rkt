#lang racket
(require tests/eli-tester)

(test
 (for ([f (in-list (list "ex-sort.rkt" "ex-file.rkt" "ex-lock.rkt" "ex-mem.rkt"))])
   (test #:failure-prefix f
         (dynamic-require f #f))))