#lang racket/base
(require racket/flonum
         ffi/unsafe
         racket/unsafe/ops)

(define-cstruct _cs
  ([x _double]
   [y _double]))

(define N 180000)
(define (test-fun)
  (define it (make-cs 1.0 2.0))
  (for/fold ([sum 0.0])
            ([i (in-range N)])
    (fl+ sum
         (fl+ (cs-x it)
              (cs-y it)))))

(define (test-check-fun)
  (define it (make-cs 1.0 2.0))
  (unless (cs? it)
    (error 'impossible))
  (for/fold ([sum 0.0])
            ([i (in-range N)])
    (fl+ sum
         (fl+ (cs-x it)
              (cs-y it)))))

(define (unsafe-cs-x it)
  (ptr-ref it _double 'abs 0))
(define (unsafe-cs-y it)
  (ptr-ref it _double 'abs 8))
(define (test-unsafe-fun)
  (define it (make-cs 1.0 2.0))
  (for/fold ([sum 0.0])
            ([i (in-range N)])
    (fl+ sum
         (fl+ (unsafe-cs-x it)
              (unsafe-cs-y it)))))

(module+ main
  (time (test-fun))
  (time (test-check-fun))
  (time (test-unsafe-fun)))
