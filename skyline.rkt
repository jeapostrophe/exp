#lang racket/base
(require data/heap)

(define (lift < f)
  (λ (x y) (< (f x) (f y))))

(define-syntax-rule (while cond body)
  (let loop () (when cond body (loop))))

(define (skyline bs)
  (define active-bs (make-heap (lift > cadr)))
  (heap-add! active-bs (list #f 0 #f))
  (define ended-bs (make-hasheq))
  (define d '())

  (define ((start b))
    (define old-max-h (cadr (heap-min active-bs)))
    (heap-add! active-bs b)
    (when (> (cadr b) old-max-h)
      (set! d (cons (list (car b) (cadr b)) d))))
  (define ((end b))
    (define old-max-h (cadr (heap-min active-bs)))
    (hash-set! ended-bs b #t)
    (while (hash-ref ended-bs (heap-min active-bs) #f)
      (heap-remove-min! active-bs))
    (define new-max-h (cadr (heap-min active-bs)))
    (unless (= old-max-h new-max-h)
      (set! d (cons (list (caddr b) new-max-h) d))))

  (define events (make-heap (lift < car)))
  (for ([b (in-list bs)])
    (heap-add! events (cons (car b) (start b)))
    (heap-add! events (cons (caddr b) (end b))))
  (for ([e (in-heap events)]) 
    ((cdr e)))
  (reverse d))

(module+ test
  (require rackunit racket/list)
  (define in
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
  (define out
    '((1 11) (3 13) (9 0) (12 7) (16 3) (19 18) (22 3) (23 13) (29 0)))
  (check-equal? (skyline in) out)
  (check-equal? (skyline (append in in)) out)
  (for ([i (in-range 10)])
    (check-equal? (skyline (shuffle in)) out)))
