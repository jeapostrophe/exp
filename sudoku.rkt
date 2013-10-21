#lang racket/base
(require racket/match
         racket/list
         racket/stream
         racket/set)

(define anything (seteq 1 2 3 4 5 6 7 8 9))
(struct cell (x y can-be) #:transparent)

(define (cell-solved? c)
  (= 1 (set-count (cell-can-be c))))

(define (floor3 x)
  (floor (/ x 3)))

(define (neighbor-of? l r)
  (or (same-row? l r)
      (same-col? l r)
      (same-box? l r)))
(define (same-box? l r)
  (and (= (floor3 (cell-x l)) (floor3 (cell-x r)))
       (= (floor3 (cell-y l)) (floor3 (cell-y r)))))
(define (same-row? l r)
  (= (cell-x l) (cell-x r)))
(define (same-col? l r)
  (= (cell-y l) (cell-y r)))

;; a grid is a list of cells

(define hrule "-----------")

;; board : string ... -> grid
(define (board . ss)
  (match-define
   (list r1 r2 r3 (== hrule)
         r4 r5 r6 (== hrule)
         r7 r8 r9)
   ss)
  (define rs
    (list r1 r2 r3 r4 r5 r6 r7 r8 r9))
  (flatten
   (for/list ([r (in-list rs)]
              [y (in-naturals)])
     (parse-row y r))))

(define (parse-row y r)
  (for/list ([c (in-string r)]
             [i (in-naturals)])
    (cond
      [(or (= i 3) (= i 7))
       (if (char=? c #\|)
         empty
         (error 'parse-row))]
      [else
       (define x
         (cond [(< i 3) (- i 0)]
               [(< i 7) (- i 1)]
               [   else (- i 2)]))
       (parse-cell y x c)])))

(define (parse-cell y x c)
  (cell x y
        (if (char=? #\space c)
          anything
          (seteq (string->number (string c))))))

(define (propagate-one top cs)
  (if (cell-solved? top)
    (for/fold ([changed? #f] [_ top] [ncs empty])
        ([c (in-list cs)])
      (cond
        [(neighbor-of? top c)
         (define before
           (cell-can-be c))
         (define after
           (set-subtract before (cell-can-be top)))
         (if (= (set-count before)
                (set-count after))
           (values changed?
                   top
                   (cons c ncs))
           (values #t
                   top
                   (cons (struct-copy cell c
                                      [can-be after])
                         ncs)))]
        [else
         (values changed? top (cons c ncs))]))
    (values #f
            top
            cs)
    #;
    (let ()
    (define before
    (cell-can-be top))
    (define after
    (for/fold ([top-cb before])
    ([n (in-sequences (in-list cs) (in-list ocs))])
    (if (same-row? top n)
    (set-subtract top-cb (cell-can-be n))
    top-cb)))
    (if (and (= 1 (set-count after))
    (not (= (set-count before)
    (set-count after))))
    (values #t
    (struct-copy cell top
    [can-be after])
    cs)
    (values #f
    top
    cs)))))

(define (find-pivot f l)
  (let loop ([tried empty]
             [to-try l])
    (match to-try
      [(list)
       (values #f l)]
      [(list-rest top more)
       (define-values (changed? ntop nmore)
         (f top (append tried more)))
       (if changed?
         (values #t (cons ntop nmore))
         (loop (cons top tried) more))])))

(define (propagate g)
  (find-pivot propagate-one g))

(define (until-fixed-point f o)
  (define-values (changed? no) (f o))
  (if changed?
    (stream-cons no (until-fixed-point f no))
    empty-stream))

;; solve-it : grid -> (listof grid)
(define (solve-it g)
  (until-fixed-point propagate g))

(require 2htdp/image
         2htdp/universe)
(define (fig s) (text s 12 "black"))
(define MIN-FIG (fig "1"))
(define CELL-W (* 3 (image-width MIN-FIG)))
(define CELL-H (* 3 (image-height MIN-FIG)))

(struct draw-state (before after))
(define (draw-it! gs)
  (define (move-right ds)
    (match-define (draw-state before after) ds)
    (if (stream-empty? (stream-rest after))
      ds
      (draw-state (cons (stream-first after) before)
                  (stream-rest after))))
  (define (draw-can-be can-be)
    (define (figi i)
      (if (set-member? can-be i)
        (fig (number->string i))
        (fig " ")))
    (place-image/align
     (if (= 1 (set-count can-be))
       (scale 3 (fig (number->string (set-first can-be))))
       (above (beside (figi 1) (figi 2) (figi 3))
              (beside (figi 4) (figi 5) (figi 6))
              (beside (figi 7) (figi 8) (figi 9))))
     0 0
     "left" "top"
     (rectangle CELL-W CELL-H
                "outline" "black")))
  (define (draw-draw-state ds)
    (match-define (draw-state before after) ds)
    (define g (stream-first after))
    (for/fold ([i
                (empty-scene (* CELL-W 11)
                             (* CELL-H 11))])
        ([c (in-list g)])
      (match-define (cell x y can-be) c)
      (place-image/align
       (draw-can-be can-be)
       (* CELL-W
          (cond [(<= x 2) (+ x 0)]
                [(<= x 5) (+ x 1)]
                [   else  (+ x 2)]))
       (* CELL-H
          (cond [(<= y 2) (+ y 0)]
                [(<= y 5) (+ y 1)]
                [   else  (+ y 2)]))
       "left" "top"
       i)))
  (big-bang (draw-state empty gs)
            (on-tick move-right 1/8)
            (on-draw draw-draw-state)))

(module+ main
  (draw-it!
   (solve-it
    (board
     "53 | 7 |   "
     "6  |195|   "
     " 98|   | 6 "
     "-----------"
     "8  | 6 |  3"
     "4  |8 3|  1"
     "7  | 2 |  6"
     "-----------"
     " 6 |   |28 "
     "   |419|  5"
     "   | 8 | 79"))))
