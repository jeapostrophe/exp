#lang racket/base
(require racket/list
         racket/match
         racket/set)

(struct ttt ())
(struct middle ttt (mover board))
(struct end ttt (winner))

(define (set-members? s l)
  (for/and ([e (in-list l)])
    (set-member? s e)))

(define (middle* p b)
  (define last (swap p))
  (define last-won?
    (for*/or ([x (in-range 3)]
              [y (in-range 3)])
      (or (set-members? b
                        (list (cons (+ x 0) y)
                              (cons (+ x 1) y)
                              (cons (+ x 2) y)))
          (set-members? b
                        (list (cons x (+ y 0))
                              (cons x (+ y 1))
                              (cons x (+ y 2))))
          (set-members? b
                        (list (cons (- x 1) (- y 1))
                              (cons x y)
                              (cons (+ x 1) (+ y 1)))))))
  (if last-won?
    (end last)
    (middle p b)))

(define initial-state
  (middle 'O (hash)))

(struct move ())
(struct place move (x y))

(define moves
  (for*/list ([x (in-range 3)]
              [y (in-range 3)])
    (place x y)))

(define swap
  (match-lambda
   ['O 'X]
   ['X 'O]))

(define (next s m)
  (match s
    [(middle p b)
     (match-define (place x y) m)
     (and (not (hash-has-key? b (cons x y)))
          (middle* (swap p) (hash-set b (cons x y) p)))]
    [(end _)
     #f]))

(define winner
  end-winner)
