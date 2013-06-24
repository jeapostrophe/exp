#lang racket/base
(require racket/list
         racket/match)
(module+ test
  (require rackunit))

(define (height-map->drawing hm)
  (define locs (sort (hash-keys hm) <))
  (define start (apply min locs))
  (define end (apply max locs))

  (define-values (lasth lasti res)
    (for/fold ([lasth 0] [lasti 0] [res empty])
        ([i (in-range 0 (add1 end))])
      (define this (hash-ref hm i 0))
      (if (= this lasth)
        (values lasth i res)
        (values this i (list* this i res)))))

  (reverse (list* 0 (add1 lasti) res)))

(module+ test
  (check-equal? (height-map->drawing (hasheq 1 4
                                             2 4))
                '(1 4 3 0)))

(define empty-hm #f)

(define (height-map-incr hm i new)
  (hash-update hm i (λ (old) (max old new)) 0))

(define (insert* b hm)
  (if b
    (insert b hm)
    hm))

(define (split b1 b2)
  (match-define (list l1 h1 r1) b1)
  (match-define (list l2 h2 r2) b2)
  (list #f b2 (list r2 h1 r1)))

(module+ test
  (check-equal? (split '(2 6 7) '(1 11 5))
                (list #f
                      '(1 11 5)
                      '(5 6 7))))

(define (insert b hm)
  (match-define (list l h r) b)
  (match hm
    [#f
     (list #f b #f)]
    [(list to-the-left (and tb (list tl _ tr)) to-the-right)
     (cond
       [(< r tl)
        (list (insert b to-the-left) tb to-the-right)]
       [(< tr l)
        (list to-the-left tb (insert b to-the-right))]
       [else
        (match-define (list nl nm nr) (split b tb))
        (list (insert* nl to-the-left)
              nm 
              (insert* nr to-the-right))])]))

(define (skyline bs)
  (foldl insert empty-hm bs))

(define (skyline* l)
  (height-map->drawing (skyline l)))

(module+ test
  (check-equal?
   (skyline*
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
   '(1 11 3 13 9 0 12 7 16 3 19 18 22 3 23 13 29 0)))