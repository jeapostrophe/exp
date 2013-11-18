#lang racket/base
(require racket/dict
         racket/match
         racket/string
         2htdp/universe
         2htdp/image)

(struct dish (rows cols gv))

(define (string->dish s)
  (define rows (string-split s))
  (define how-many-rows (* 2 (length rows)))
  (define the-gv (make-vector how-many-rows #f))
  (define how-many-cols
    (* 2 (apply max (map string-length rows))))
  (for ([i (in-range how-many-rows)])
    (define rv (make-bytes how-many-cols))
    (vector-set! the-gv i rv))
  (for ([i (in-naturals)]
        [r (in-list rows)])
    (define rv (vector-ref the-gv i))
    (for ([j (in-naturals)]
          [c (in-string r)])
      (vector-set! rv j (char=? #\O c))))
  (dish how-many-rows how-many-cols
        the-gv))

(define (live? gv i j)
  (define rn (vector-ref gv i))
  (vector-ref rn j))

(define (neighbors max-i max-j gv i j)
  (for*/fold ([cnt 0])
      ([di (in-list (list -1 0 +1))]
       #:when (<= 0 (+ di i) (sub1 max-i))
       [dj (in-list (list -1 0 +1))]
       #:when (<= 0 (+ dj j) (sub1 max-j))
       #:unless (and (= di 0) (= dj 0)))
    (if (live? gv (+ di i) (+ dj j))
      (add1 cnt)
      cnt)))

(define (tick d)
  (match-define (dish rs cs old-gv) d)
  (define new-gv (make-vector rs #f))
  (for ([i (in-range rs)])
    (vector-set!
     new-gv i
     (for/vector ([j (in-range cs)])
       (define alive? (live? old-gv i j))
       (define ns (neighbors rs cs old-gv i j))
       (define new-alive?
         (or (and alive? (or (= ns 2) (= ns 3)))
             (and (not alive?) (= ns 3))))
       new-alive?)))
  (dish rs cs new-gv))

(define (draw d)
  (match-define (dish rs cs gv) d)
  (scale
   10
   (apply
    above/align
    'left
    (for/list ([r (in-vector gv)])
      (apply
       beside/align
       'bottom
       (for/list ([j (in-vector r)])
         (square 1 (if j "solid" "outline") "black")))))))

(define (let-there-be-life s)
  (big-bang (string->dish s)
            [on-tick tick]
            [on-draw draw]))

(module+ test
  (let-there-be-life
   "........................O...........
    ......................O.O...........
    ............OO......OO............OO
    ...........O...O....OO............OO
    OO........O.....O...OO..............
    OO........O...O.OO....O.O...........
    ..........O.....O.......O...........
    ...........O...O....................
    ............OO......................"))
