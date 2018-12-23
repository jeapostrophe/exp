#lang racket/base
(require racket/fixnum
         racket/unsafe/ops)

;; XXX make package

(define (ctz x)
  (cond
    [(fx= x 0) 32]
    [else
     (define n 0)
     (define-syntax-rule (round cm mod)
       (when (zero? (unsafe-fxand x cm))
         (set! n (unsafe-fx+ n mod))
         (set! x (unsafe-fxrshift x mod))))
     (round #x0000FFFF 16)
     (round #x000000FF  8)
     (round #x0000000F  4)
     (round #x00000003  2)
     (round #x00000001  1)
     n]))

(define 2^32 4294967087)
(define (random-32)
  (random 2^32))

(module+ test
  (define counts (make-hasheq))
  (for ([i (in-range 1000)])
    (hash-update! counts (ctz (random-32)) add1 0))
  (require racket/pretty)
  (pretty-print counts))
