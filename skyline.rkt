#lang racket/base
(require racket/list
         data/heap
         racket/match)

(define (skyline bs)
  (define (lift <= f)
    (λ (x y)
      (<= (f x) (f y))))

  (define evt-pos
    (match-lambda
     [(cons 'start (list l h r)) l]
     [(cons 'end (list l h r)) r]))
  (define events (make-heap (lift <= evt-pos)))
  (for ([b (in-list bs)])
    (heap-add! events (cons 'start b))
    (heap-add! events (cons 'end b)))

  (define heights (make-heap (lift > second)))
  (heap-add! heights (list -inf.0 0 +inf.0))

  (define ended-bs (make-hasheq))

  (define-values (d)
    (for/fold ([d empty]) ([e (in-heap events)])
      (match e
        [(cons 'start (and b (list l h r)))
         (match-define (list _ max-h _) (heap-min heights))
         (heap-add! heights b)
         (if (> h max-h)
           (cons (list l h) d)
           d)]
        [(cons 'end (and b (list l h r)))
         (hash-set! ended-bs b #t)

         (match-define (list _ old-max-h _) (heap-min heights))

         (let loop ()
           (define max-b (heap-min heights))
           (when (hash-ref ended-bs max-b #f)
             (heap-remove-min! heights)
             (loop)))

         (match-define (list _ new-max-h _) (heap-min heights))

         (if (= old-max-h new-max-h)
           d
           (cons (list r new-max-h) d))])))
  (reverse d))

(module+ test
  (require rackunit)
  (define in
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
  (define out
    '((1 11) (3 13) (9 0) (12 7) (16 3) (19 18) (22 3) (23 13) (29 0)))
  (check-equal? (skyline in) out)
  (for ([i (in-range 10)])
    (check-equal? (skyline (shuffle in)) out)))
