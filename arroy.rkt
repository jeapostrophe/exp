#lang racket/base
(require racket/list
         racket/match
         racket/set
         racket/unit
         racket/function)

;; A labelled transition system is a...
;;  initial-state : state
;;  moves         : (listof moves)
;;  next          : state move -> Maybe state
;;  winner        : state -> player
;;  player        : state -> player
(define-signature lts^
  (initial-state moves next winner player))

;; Tic-Tac-Toe is an example of an LTS
(define-unit ttt@
  (import)
  (export lts^)

  ;; The game is either in the middle or at the end
  (struct ttt () #:transparent)
  (struct middle ttt (mover board) #:transparent)
  (struct end ttt (winner) #:transparent)

  (define player
    (match-lambda
     [(middle m _) m]
     [(end w) w]))

  ;; A smart constructor that detects when the game is over. Could be
  ;; more efficient.
  (define (middle* p b)
    (define last (swap p))
    (define (set-members? s l)
      (for/and ([e (in-list l)])
        (equal? (hash-ref s e #f) last)))
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
    (define board-full?
      (for*/and ([x (in-range 3)]
                 [y (in-range 3)])
        (hash-has-key? b (cons x y))))
    (cond
      [board-full?
       (end #f)]
      [last-won?
       (end last)]
      [else
       (middle p b)]))

  (define initial-state
    (middle 'O (hash)))

  ;; There's only one kind of a move, placing your mark.
  (struct move () #:transparent)
  (struct place move (x y) #:transparent)

  (define moves
    (for*/list ([x (in-range 3)]
                [y (in-range 3)])
      (place x y)))

  (define swap
    (match-lambda
     ['O 'X]
     ['X 'O]))

  ;; You can only place in the middle of the game and only if the
  ;; square is not occupied.
  (define (next s m)
    (match s
      [(middle p b)
       (match-define (place x y) m)
       (and (not (hash-has-key? b (cons x y)))
            (middle* (swap p) (hash-set b (cons x y) p)))]
      [(end _)
       #f]))

  (define winner
    end-winner))

;; Guess a number between 0 and 9
(define-unit guess@
  (import)
  (export lts^)

  ;; You're either choosing, guessing, or the game is over
  (struct choose () #:transparent)
  (struct guess (i) #:transparent)
  (struct won () #:transparent)
  (struct lost () #:transparent)

  ;; You always choose first
  (define initial-state
    (choose))

  ;; You can only pick a number
  (struct pick (i) #:transparent)

  (define moves
    (for/list ([i (in-range 10)])
      (pick i)))

  (define next
    (match-lambda*
     ;; If you are choosing, then a pick results in a guess
     [(list (choose) (pick i))
      (guess i)]
     ;; If you pick the guess, then you won
     [(list (guess i) (pick i))
      (won)]
     ;; Or you lost
     [(list (guess i) (pick j))
      (lost)]
     ;; Or you can't do anything
     [_
      #f]))

  (define winner
    (match-lambda
     [(won) 'guesser]
     [(lost) 'picker]))

  (define player
    (match-lambda
     [(choose) 'picker]
     [(guess _) 'guesser]
     [x (winner x)])))

;; Arroy takes an LTS and presents a stepper for it, but it also
;; annotates that options with whether the current player can win.
(define-unit arroy@
  (import lts^)
  (export)

  (define (available s)
    (filter-map
     (λ (m)
       (define ns (next s m))
       (and ns (cons m ns)))
     moves))

  (define (can-win? p s)
    (match (available s)
      [(list)
       (equal? p (winner s))]
      [a
       (ormap (compose (curry can-win? p) cdr) a)]))

  (let loop ([s initial-state])
    (printf "Current state: ~a\n"
            s)
    (match (available s)
      [(list)
       (printf "Winner: ~a\n"
               (winner s))]
      [a
       (printf "Available moves:\n")
       (for ([m*ns (in-list a)]
             [i (in-naturals)])
         (printf "\t~a. ~a (~a)\n"
                 i (car m*ns)
                 (can-win? (player s) (cdr m*ns))))
       (printf "Selection: ") (flush-output)
       (define i (read))
       (loop (cdr (list-ref a i)))])))

(module+ main
  ;; Play Tic-Tac-Toe
  ;;(invoke-unit/infer (link ttt@ arroy@))
  ;; Play Guess
  (invoke-unit/infer (link guess@ arroy@))
  )
