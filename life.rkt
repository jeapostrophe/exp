#lang racket/base
(require racket/match
         racket/unsafe/ops
         racket/performance-hint)

(struct dish (rows cols cur nxt) #:mutable)

(define (make-dishv rs cs)
  (make-bytes (* rs cs)))
(define-inline (dishv-set! dv rs i j ?)
  (unsafe-bytes-set! dv (unsafe-fx+ i (unsafe-fx* rs j)) (if ? 1 0)))
(define-inline (dishv-ref dv rs i j)
  (unsafe-fx= 1 (unsafe-bytes-ref dv (unsafe-fx+ i (unsafe-fx* rs j)))))

(define (string->dish s)
  (local-require racket/string)
  (define rows (string-split s))
  (define rs
    (* 2 (length rows)))
  (define cs
    (* 1 (apply max (map string-length rows))))
  (define cur (make-dishv rs cs))
  (define nxt (make-dishv rs cs))

  (for ([i (in-naturals)]
        [r (in-list rows)])
    (for ([j (in-naturals)]
          [c (in-string r)])
      (dishv-set! cur rs i j (char=? #\O c))))

  (dish rs cs cur nxt))

(define-syntax-rule (unsafe-between min x max)
  (and (unsafe-fx<= min x)
       (unsafe-fx< x max)))
(define-inline (neighbors gv rs cs i j)
  (let ([cnt 0])
    (for ([di (in-range -1 +2)])
      (let ([ni (unsafe-fx+ di i)])
        (when (unsafe-between 0 ni rs)
          (for ([dj (in-range -1 +2)])
            (unless (and (unsafe-fx= di 0) (unsafe-fx= dj 0))
              (let ([nj (unsafe-fx+ dj j)])
                (when (and (unsafe-between 0 nj cs)
                           (dishv-ref gv rs ni nj))
                  (set! cnt (unsafe-fx+ 1 cnt)))))))))
    cnt))

(define (tick d)
  (match-define (dish rs cs cur nxt) d)
  (for* ([i (in-range rs)]
         [j (in-range cs)])
    (define alive? (dishv-ref cur rs i j))
    (define ns (neighbors cur rs cs i j))
    (define new-alive?
      (or (and alive? (or (unsafe-fx= ns 2) (unsafe-fx= ns 3)))
          (and (not alive?) (unsafe-fx= ns 3))))
    (dishv-set! nxt rs i j new-alive?))
  (set-dish-cur! d nxt)
  (set-dish-nxt! d cur)
  d)

(module+ test-bench
  ;;      original: cpu time: 1843 real time: 1842 gc time: 36
  ;; dishv-ref/set: cpu time: 1683 real time: 1682 gc time: 82
  ;;     neighbors: cpu time:  530 real time:  531 gc time: 0
  (define (let-there-be-life s)
    (define seed (string->dish s))
    (collect-garbage)
    (collect-garbage)
    (time
     (for ([i (in-range 10000)])
       (tick seed)))))

(module+ test
  (require 2htdp/universe
           2htdp/image)

  (define (draw d)
    (match-define (dish rs cs cur _) d)
    (define SCALE 10)
    (define BOX
      (square SCALE "solid" "black"))
    (for*/fold ([img (empty-scene
                      (* SCALE cs)
                      (* SCALE rs))])
        ([i (in-range rs)]
         [j (in-range cs)])
      (if (dishv-ref cur rs i j)
        (place-image BOX 
                     (+ (/ SCALE 2) 0.5 (* j SCALE))
                     (+ (/ SCALE 2) 0.5 (* i SCALE))
                     img)
        img)))

  (define (let-there-be-life s)
    (big-bang (string->dish s)
              [on-tick tick]
              [on-draw draw])))

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

;; xxx run on GPU?
;; xxx use bit packing on a row?
