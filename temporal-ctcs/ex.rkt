#lang racket
(require tests/eli-tester)

(test
 (for ([f (in-list (list "ex-sort.rkt" "ex-file.rkt"))])
   (dynamic-require f #f)))