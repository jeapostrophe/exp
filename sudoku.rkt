#lang racket/base
(require racket/match
         racket/list
         racket/set)

(define anything (seteq 1 2 3 4 5 6 7 8 9))
(struct cell (x y can-be) #:transparent)

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

;; solve-it! : grid -> void
(define (solve-it! g)
  g)

(require 2htdp/image
         2htdp/universe)
(define MIN-FIG (text "1" 12 "black"))
(define CELL-W (* 3 (image-width MIN-FIG)))
(define CELL-H (* 3 (image-height MIN-FIG)))

(struct draw-state (i gs))
(define (draw-it! gs)
  (define (move-left ds)
    (match-define (draw-state i gs) ds)
    (draw-state (modulo (add1 i) (length gs)) gs))
  (define (draw-can-be can-be)
    (above (beside MIN-FIG MIN-FIG MIN-FIG)
           (beside MIN-FIG MIN-FIG MIN-FIG)
           (beside MIN-FIG MIN-FIG MIN-FIG)))
  (define (draw-draw-state ds)
    (match-define (draw-state i gs) ds)
    (define g (list-ref gs i))
    (for/fold ([i
                (empty-scene (* CELL-W 11)
                             (* CELL-H 11))])
        ([c (in-list g)])
      (match-define (cell x y can-be) c)
      (place-image (draw-can-be can-be)
                   (* CELL-W
                      (cond [(<= x 2) (+ x 0)]
                            [(<= x 5) (+ x 1)]
                            [   else  (+ x 2)]))
                   (* CELL-H
                      (cond [(<= y 2) (+ y 0)]
                            [(<= y 5) (+ y 1)]
                            [   else  (+ y 2)]))
                   i)))
  (big-bang (draw-state 0 gs)
            (on-tick move-left 1)
            (on-draw draw-draw-state)))

(module+ main
  (draw-it!
   (solve-it!
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
