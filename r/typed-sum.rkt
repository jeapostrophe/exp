#lang typed/racket/base

(: sum ((Vectorof Float) -> Float))
(define (sum v)
  (for/fold: ([sum : Float 0.0])
      ([e (in-vector v)])
    (+ sum e)))

(define the-v
  (build-vector 100000 (λ (i) (+ (random 5) .1))))

(collect-garbage) (collect-garbage) (collect-garbage)

(time 
 (for ([i (in-range 10000)])
   (sum the-v)))

;; Results on my Macbook Air (Linux 2.13 GHz Core2 Duo 4GB RAM)
;; cpu time: 7324 real time: 7322 gc time: 288
;; This beats everything from R's built-in sum and up
