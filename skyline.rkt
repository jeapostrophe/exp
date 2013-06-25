#lang racket/base
(require racket/list
         data/heap
         racket/match)
(module+ test
  (require rackunit))

(define (skyline bs)
  (define (lift <= f)
    (λ (x y)
      (<= (f x) (f y))))

  (struct evt (pos b polarity))
  (define events (make-heap (lift <= evt-pos)))
  (for ([b (in-list bs)])
    (match-define (list l h r) b)
    (heap-add! events (evt l b 'start))
    (heap-add! events (evt r b 'end)))

  (struct past (h b))
  (define heights (make-heap (lift > past-h)))
  (heap-add! heights (past 0 #f))

  (define visited-bs (make-hasheq))

  (define-values (d)
    (for/fold ([d empty])
        ([e (in-heap events)])
      (match e
        [(evt pos (and b (list l h r)) 'start)
         (match-define (past max-h max-b) (heap-min heights))
         (heap-add! heights (past h b))
         (if (> h max-h)
           (cons (list l h) d)
           d)]
        [(evt pos (and b (list l h r)) 'end)
         (hash-set! visited-bs b #t)

         (match-define (past old-max-h _) (heap-min heights))

         (let loop ()
           (match-define (past max-h max-b) (heap-min heights))
           (when (hash-ref visited-bs max-b #f)
             (heap-remove-min! heights)
             (loop)))

         (match-define (past new-max-h _) (heap-min heights))

         (if (= old-max-h new-max-h)
           d
           (cons (list r new-max-h) d))])))
  (reverse d))

(module+ test
  (check-equal?
   (skyline
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
   '((1 11) (3 13) (9 0) (12 7) (16 3) (19 18) (22 3) (23 13) (29 0))))
