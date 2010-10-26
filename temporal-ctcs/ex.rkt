#lang racket
(require tests/eli-tester)

(test
 (for ([f (in-list (list "ex-sort.rkt" "ex-file.rkt" "ex-lock.rkt"))])
   (dynamic-require f #f)))