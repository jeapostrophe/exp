#lang racket/base

(define (sum v)
  (for/fold ([sum 0.0])
      ([e (in-vector v)])
    (+ sum e)))

(define the-v
  (build-vector 100000 (λ (i) (+ (random 5) .1))))

(collect-garbage) (collect-garbage) (collect-garbage)

(time 
 (for ([i (in-range 10000)])
   (sum the-v)))

;; Results on my Macbook Air (Linux 2.13 GHz Core2 Duo 4GB RAM)
;; cpu time: 15140 real time: 15373 gc time: 1424
;; This beats everything from Python's built-in sum() and up
