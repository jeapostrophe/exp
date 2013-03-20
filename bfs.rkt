#lang racket
(require data/queue)

(define (enqueue!* q l)
  (for-each (curry enqueue! q) l))

(define (bfs ? node-data node-children root)
  (define q (make-queue))
  (let visit ([n root])
    (cond
      [(? (node-data n))
       n]
      [else
       (enqueue!* q (node-children n))
       (cond
         [(queue-empty? q)
          #f]
         [else
          (visit (dequeue! q))])])))

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

  (bfs (λ (x)
         (printf "Visited ~a\n" x)
         (= x 11))
       first
       rest
       d)

  (bfs (λ (x)
         (printf "Visited ~a\n" x)
         (= x 11))
       (λ (x) x)
       (λ (x)
         (list (+ (* 2 x) 0)
               (+ (* 2 x) 1)))
       1))
