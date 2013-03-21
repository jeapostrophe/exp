#lang racket/base
(require racket/list
         data/heap)

(define (heap-empty? h)
  (zero? (heap-count h)))

(define (best-first-search node-data node-children node-score ? root)
  (define (node-<= x y)
    (<= (node-score x) (node-score y)))
  (define q (make-heap node-<=))
  (let visit ([i 0] [n root])
    (cond
      [(? (node-data n))
       (eprintf "found after ~a\n" i)
       n]
      [else
       (heap-add-all! q (node-children n))
       (cond
         [(heap-empty? q)
          #f]
         [else
          (define next (heap-min q))
          (heap-remove-min! q)
          (visit (add1 i) next)])])))

(define (bfs node-data node-children ? root)
  (best-first-search
   node-data node-children
   (λ (n) 0)
   ?
   root))

(define (dfs node-data node-children ? root)
  (cdr
   (best-first-search
    (λ (d*n) (node-data (cdr d*n)))
    (λ (d*n) (map (λ (c) (cons (add1 (car d*n)) c))
                  (node-children (cdr d*n))))
    (λ (d*n) (* -1 (car d*n)))
    ?
    (cons 0 root))))

(module+ main
  (define d
    '(1
      (2
       (3
        (4)
        (5)
        (6
         (7)
         (8))
        (9)
        (10)
        (11
         (12))
        (13))
       (14
        (15))
       (16
        (17))
       (18
        (19))
       (20))
      (21)))

  (define look-for-11
    (λ (x)
      (printf "Visited ~a\n" x)
      (= x 11)))

  (bfs first
       rest
       look-for-11
       d)

  (bfs (λ (x) x)
       (λ (x) (list (+ (* 2 x) 0)
                    (+ (* 2 x) 1)))
       look-for-11
       1)

  (dfs first
       rest
       look-for-11
       d)

  (dfs (λ (x) x)
       (λ (x)
         (if (> x 150)
           empty
           (list (+ (* 2 x) 0)
                 (+ (* 2 x) 1))))
       look-for-11
       1)

  (best-first-search
   first
   rest
   (λ (x) (abs (- (first x) 11)))
   look-for-11
   d)

  (best-first-search
   (λ (x) x)
   (λ (x) (list (+ (* 2 x) 0)
                (+ (* 2 x) 1)))
   (λ (x) (abs (- x 11)))
   look-for-11
   1))
