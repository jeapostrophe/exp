#lang racket/base
(require racket/list
         data/heap
         racket/match)

(define (lift <= f)
  (λ (x y)
    (<= (f x) (f y))))

(define-syntax-rule (while cond body ...)
  (let loop () (when cond body ... (loop))))

(define (skyline bs)
  (define active-bs (make-heap (lift > second)))
  (heap-add! active-bs (list -inf.0 0 +inf.0))
  (define ended-bs (make-hasheq))
  (define d empty)

  (define ((start b))
    (match-define (list l h r) b)
    (match-define (list _ old-max-h _) (heap-min active-bs))
    (heap-add! active-bs b)
    (when (> h old-max-h)
      (set! d (cons (list l h) d))))
  (define ((end b))
    (match-define (list l h r) b)
    (match-define (list _ old-max-h _) (heap-min active-bs))
    (hash-set! ended-bs b #t)
    (while (hash-ref ended-bs (heap-min active-bs) #f)
      (heap-remove-min! active-bs))
    (match-define (list _ new-max-h _) (heap-min active-bs))
    (unless (= old-max-h new-max-h)
      (set! d (cons (list r new-max-h) d))))

  (define events (make-heap (lift <= car)))
  (for ([b (in-list bs)])
    (match-define (list l h r) b)
    (heap-add! events (cons l (start b)))
    (heap-add! events (cons r (end b))))
  (for ([e (in-heap events)]) ((cdr e)))
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
