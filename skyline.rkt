#lang racket/base
(require data/heap)

(define (skyline bs)
  (define abs (make-heap (lift > cadr)))
  (heap-add! abs (list 0 0 0))
  (define ebs (make-hasheq))
  (define d '())

  (define ((start b) omh)
    (heap-add! abs b)
    (when (> (cadr b) omh)
      (set! d (cons (list (car b) (cadr b)) d))))
  (define ((end b) omh)
    (hash-set! ebs b 1)
    (while (hash-ref ebs (heap-min abs) #f)
      (heap-remove-min! abs))
    (define nmh (cadr (heap-min abs)))
    (unless (= omh nmh)
      (set! d (cons (list (caddr b) nmh) d))))

  (define es (make-heap (lift < car)))
  (for ([b (in-list bs)])
    (heap-add! es (cons (car b) (start b)))
    (heap-add! es (cons (caddr b) (end b))))
  (for ([e (in-heap es)])
    ((cdr e) (cadr (heap-min abs))))
  (reverse d))

(define (lift < f)
  (λ (x y) (< (f x) (f y))))

(define-syntax-rule (while C B)
  (let L () (when C B (L))))

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
