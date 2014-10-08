#lang racket
(require math/base
         plot)

(define (insert-cost n inverted?)
  (if inverted?
      n
      1))

(define (isort-cost n is)
  (cond
   [(zero? n)
    0]
   [else
    (+ (insert-cost (sub1 n) (first is))
       (isort-cost (sub1 n) (rest is)))]))

(define (average l)
  (if (empty? l)
      0
      (/ (sum l) (length l))))

(define (list-with-m-trues-and-n-elements n m)
  (build-list n (λ (x) (< x m))))

(define (perms-with-m-trues-and-n-elements n m)
  (remove-duplicates (permutations (list-with-m-trues-and-n-elements n m))))

(module+ main
  (plot-new-window? #t)
  (parameterize ([plot-title  "Insertion Sort Cost"]
                 [plot-x-label "n"]
                 [plot-y-label "i"]
                 [plot-z-label "cost"])
    (plot3d
     (contour-intervals3d (λ (n i)
                            (argmax (λ (x) x)
                             (map (λ (p)
                                    (isort-cost (floor n) p))
                                  (perms-with-m-trues-and-n-elements (floor n) (floor (min n i))))))
                          0 8
                          0 8))
    (plot3d
     (contour-intervals3d (λ (n i)
                            (* n n))
                          0 8
                          0 8))))
