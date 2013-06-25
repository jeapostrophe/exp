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

  (define active-bs (make-heap (lift > second)))
  (heap-add! active-bs (list -inf.0 0 +inf.0))

  (define ended-bs (make-hasheq))

  (define d empty)
  (for ([e (in-heap events)])
    (match-define (cons pol (and b (list l h r))) e)
    (match-define (list _ old-max-h _) (heap-min active-bs))
    (match pol
      ['start
       (heap-add! active-bs b)
       (when (> h old-max-h)
         (set! d (cons (list l h) d)))]
      ['end
       (hash-set! ended-bs b #t)
       (let loop ()
         (define max-b (heap-min active-bs))
         (when (hash-ref ended-bs max-b #f)
           (heap-remove-min! active-bs)
           (loop)))
       (match-define (list _ new-max-h _) (heap-min active-bs))
       (unless (= old-max-h new-max-h)
         (set! d (cons (list r new-max-h) d)))]))
  (reverse d))

(module+ test
  (require rackunit)
  (define in
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
  (define out
    '((1 11) (3 13) (9 0) (12 7) (16 3) (19 18) (22 3) (23 13) (29 0)))
  (check-equal? (skyline in) out)
  (check-equal? (skyline (append in in)) out)
  (for ([i (in-range 10)])
    (check-equal? (skyline (shuffle in)) out)))
