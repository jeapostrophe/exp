#lang racket/base
(require racket/contract
         racket/match)
(module+ test
  (require rackunit))

;; A space is #f, 'X, or 'O
(define space/c
  (or/c false/c 'X 'O))

;; A board is a (hasheq (hasheq space space space) x 3)
(define posn/c
  (or/c 0 1 2))
(define board/c
  (hash/c posn/c
          (hash/c posn/c
                  space/c
                  #:immutable #t)
          #:immutable #t))

(define empty-board
  (hasheq 0 (hasheq 0 #f 1 #f 2 #f)
          1 (hasheq 0 #f 1 #f 2 #f)
          2 (hasheq 0 #f 1 #f 2 #f)))

(module+ test
  (define winning-o-board/col
    (hasheq 0 (hasheq 0 'O 1 #f 2 #f)
            1 (hasheq 0 'O 1 #f 2 #f)
            2 (hasheq 0 'O 1 #f 2 #f)))
  (define winning-x-board/row
    (hasheq 0 (hasheq 0 'O 1 #f 2 #f)
            1 (hasheq 0 'X 1 'X 2 'X)
            2 (hasheq 0 'O 1 #f 2 #f)))
  (define winning-x-board/left
    (hasheq 0 (hasheq 0 'X 1 #f 2 #f)
            1 (hasheq 0 'O 1 'X 2 'X)
            2 (hasheq 0 'O 1 #f 2 'X)))
  (define winning-o-board/right
    (hasheq 0 (hasheq 0 'X 1 #f 2 'O)
            1 (hasheq 0 'O 1 'O 2 'X)
            2 (hasheq 0 'O 1 #f 2 'X))))

(define (board-ref b r c)
  (hash-ref (hash-ref b r) c))

(module+ test
  (check-false (board-ref empty-board 0 0))
  (check-equal? (board-ref winning-o-board/right 1 2) 'X))

(define equal?*
  (match-lambda*
   [(list) #t]
   [(list e) e]
   [(list* e1 e2 es)
    (and (equal? e1 e2)
         (apply equal?* e2 es))]))

(module+ test
  (check-true (equal?*))
  (check-equal? (equal?* 1) 1)
  (check-equal? (equal?* 1 1) 1)
  (check-equal? (equal?* 1 1 1) 1)
  (check-false (equal?* 1 1 1 2)))

(define (winning-board? b)
  (or
   ;; Cols
   (for/or ([c (in-range 3)])
     (equal?*
      (board-ref b 0 c)
      (board-ref b 1 c)
      (board-ref b 2 c)))
   ;; Rows
   (for/or ([r (in-range 3)])
     (equal?*
      (board-ref b r 0)
      (board-ref b r 1)
      (board-ref b r 2)))
   ;; Left diagonal
   (equal?* (board-ref b 0 0)
            (board-ref b 1 1)
            (board-ref b 2 2))
   ;; Right diagonal
   (equal?* (board-ref b 0 2)
            (board-ref b 1 1)
            (board-ref b 2 0))))

(module+ test
  (check-false (winning-board? empty-board))

  (check-equal? (winning-board? winning-o-board/col) 'O)
  (check-equal? (winning-board? winning-x-board/row) 'X)
  (check-equal? (winning-board? winning-x-board/left) 'X)
  (check-equal? (winning-board? winning-o-board/right) 'O))

(define (board-set b r c m)
  #;(printf "b[~a][~a] = ~a\n" r c m)
  (hash-update b r (λ (r) (hash-set r c m))))

(module+ test
  (check-equal?
   (board-set
    (board-set
     (board-set empty-board
                0 0 'O)
     1 0 'O)
    2 0 'O)
   winning-o-board/col))

(define (full-board? b)
  (for/and ([r (in-range 3)]
            [c (in-range 3)])
    (board-ref b r c)))

(module+ test
  (check-not-false
   (full-board?
    (for/fold ([b empty-board])
        ([r (in-range 3)]
         [c (in-range 3)])
      (board-set b r c 'X)))))

(define (tic-tac-toe-loop
         board
         o-player x-player
         winner game-over)
  (cond
    [(winning-board? board)
     => winner]
    [(full-board? board)
     (game-over)]
    [else
     (tic-tac-toe-loop
      (o-player board board-ref board-set)
      x-player o-player
      winner game-over)]))

(define (tic-tac-toe o-player x-player
                     winner game-over)
  (tic-tac-toe-loop
   empty-board
   o-player x-player
   winner game-over))
