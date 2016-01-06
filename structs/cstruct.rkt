#lang racket/base
(require racket/flonum
         ffi/unsafe
         racket/unsafe/ops)

(define-cstruct _cs
  ([x _double]
   [y _double])
  #:define-unsafe)

(define N 180000)
(define (test-fun)
  (define it (make-cs 1.0 2.0))
  (for/fold ([sum 0.0])
            ([i (in-range N)])
    (fl+ sum
         (fl+ (cs-x it)
              (cs-y it)))))

cs-x-offset
cs-y-offset

(define (test-unsafe-fun)
  (define it (make-cs 1.0 2.0))
  (for/fold ([sum 0.0])
            ([i (in-range N)])
    (fl+ sum
         (fl+ (unsafe-cs-x it)
              (unsafe-cs-y it)))))

(module+ main
  (time (test-fun))
  (time (test-unsafe-fun)))
