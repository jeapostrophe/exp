#lang racket/base
(require racket/list
         racket/match)
(module+ test
  (require rackunit))

(struct building (left height right) #:transparent)

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

(define (skyline* l)
  ;; xxx what about linear time?
  (height-map->drawing (skyline (map (λ (l) (apply building l)) l))))

(define empty-hm (hasheq))

(define (height-map-incr hm i new)
  (hash-update hm i (λ (old) (max old new)) 0))

(define (insert b hm)
  (match-define (building l h r) b)
  (for/fold ([hm hm])
      ;; xxx what about non-reals?
      ([i (in-range l r)])    
    (height-map-incr hm i h)))

(define (skyline bs)
  (cond
    [(empty? bs)
     empty-hm]
    [else
     (insert (first bs) (skyline (rest bs)))]))

(module+ test
  (when #f
    (check-equal? (insert (building 0 3 4) empty)
                  '(0 3 4 0))

    ;; Un-obscured
    (check-equal? (insert (building 0 3 4) '(5 6 7 0))
                  '(0 3 4 0 5 6 7 0))

    ;; Obscured on left
    (check-equal? (insert (building 6 2 8) '(5 3 7 0))
                  '(0 5 2 6 3 8 0))

    ;; Obscured on right
    (check-equal? (insert (building 5 2 7) '(6 3 8 0))
                  '(0 5 2 6 3 8 0))

    ;; Totally obscured
    (check-equal? (insert (building 0 2 3) '(1 1 2 0))
                  '(0 2 3 0))

    (check-equal? (insert (building 23 13 29) '(24 4 28 0))
                  '(23 13 29 0)))

  (check-equal?
   (skyline*
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
   '(1 11 3 13 9 0 12 7 16 3 19 18 22 3 23 13 29 0)))
