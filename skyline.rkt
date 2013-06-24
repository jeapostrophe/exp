#lang racket/base
(require racket/list
         racket/match)
(module+ test
  (require rackunit))

(struct building (left height right) #:transparent)

(define (skyline* l)
  (skyline (map (λ (l) (apply building l)) l)))

(define (building-at:height i os)
  (printf "~a\n" (list 'building-at:right i os))
  (cond
    [(empty? os)
     0]
    [else
     (match os
       [(list r 0)
        0]
       [(list* l h r more)
        (if (<= l i r)
          h
          (building-at:height i (list* r more)))])]))

(define (building-at:right i os)
  (cond
    [(empty? os)
     (error 'building-at:right "No building at ~e" i)]
    [else
     (match-define (list* l h r more) os)
     (if (<= l i r)
       r
       (building-at:right i (list* r more)))]))

(define (insert b os)
  (match-define (building l h r) b)
  (cond
    [(< r l)
     os]
    [(empty? os)
     (list l h r 0)]
    [else
     (match os
       [(list last-r 0)
        (if (< l last-r)

          )]
       )]

    [(> (building-at:height l os) h)
     (insert (building (building-at:right l os) h r) os)]
    [else
     (error 'insert "Don't know how to deal with ~v in ~v\n" b os)]))

(define (skyline bs)
  (cond
    [(empty? bs)
     empty]
    [else
     (insert (first bs) (skyline (rest bs)))]))

(module+ test
  (check-equal? (insert (building 0 3 4) empty)
                '(0 3 4 0))

  ;; Un-obscured
  (check-equal? (insert (building 0 3 4) '(5 6 7 0))
                '(0 3 4 0 5 6 7 0))

  ;; Obscured on left
  (check-equal? (insert (building 6 3 8) '(5 2 7 0))
                '(0 5 2 6 3 8 0))

  ;; Obscured on right
  (check-equal? (insert (building 5 2 7) '(6 3 8 0))
                '(0 5 2 6 3 8 0))

  ;; Totally obscured
  (check-equal? (insert (building 0 2 3) '(1 1 2 0))
                '(0 2 3 0))

  (check-equal? (insert (building 23 13 29) '(24 4 28 0))
                '(23 13 29 0))

  (check-equal?
   (skyline*
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
   '(1 11 3 13 9 0 12 7 16 3 19 18 22 3 23 13 29 0)))
