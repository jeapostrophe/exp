#lang racket
(require racket/runtime-path
         racket/generator)

;; dictionary : char -> bool x dictionary
(define empty-dict (hasheq))
(define empty-entry (cons #f empty-dict))
(define (dict-add d w)
  (if (empty? w)
    empty-dict
    (hash-update d (first w)
                 (match-lambda
                  [(cons word? rest-d)
                   (cons (or word? (empty? (rest w)))
                         (dict-add rest-d (rest w)))])
                 empty-entry)))

;; parse the standard dictionary into this format
(define-runtime-path dict-pth "/usr/share/dict/words")
(define the-dictionary
  (with-input-from-file dict-pth
    (λ ()
      (for/fold ([d empty-dict])
          ([w (in-lines)])
        (dict-add d (string->list w))))))

;; generate a random board of a certain square size
(define board-n 4)
(define letters
  (string->list
   "abcdefghijklmnopqrstuvwxyz"))
(define (random-list-ref l)
  (list-ref l (random (length l))))
(define board
  (for*/fold ([cell->char (hash)])
      ([row (in-range board-n)]
       [col (in-range board-n)])
    (define cell (cons row col))
    (hash-set cell->char cell
              (random-list-ref letters))))

;; print out the board so you can see it
(for ([row (in-range board-n)])
  (for ([col (in-range board-n)])
    (printf "~a" (hash-ref board (cons row col))))
  (printf "\n"))
(printf "\n")

;; find all solutions from a certain cell in this board, with a given
;; dictionary and prefix
(define (solutions-from board dict k prefix)
  ;; find the character at the cell
  (define c (hash-ref board k #f))
  ;; if the cell isn't in the board, then stop the cell won't be in
  ;; the board if it never was (like (-1,8)) or if it has been
  ;; visited, and thus removed
  (when c
    ;; look up the character in the dictionary
    (match-define (cons word? next-dict)
                  (hash-ref dict c empty-entry))
    ;; find the new word prefix
    (define next-prefix (cons c prefix))
    ;; if it is a valid word, turn it into a string and 'yield' it.
    (when word?
      (yield (list->string (reverse next-prefix))))
    ;; if the prefix dictionary is not empty
    (unless (zero? (hash-count next-dict))
      ;; ignore this cell in the future
      (define next-board (hash-remove board k))
      (match-define (cons row col) k)
      (for* ([drow (in-list '(-1 0 1))]
             [dcol (in-list '(-1 0 1))])
        ;; consider all adjacent squares
        (solutions-from next-board next-dict
                        (cons (+ row drow)
                              (+ col dcol))
                        next-prefix)))))

;; start looking for a solution from every cell
(define (solutions board dict)
  (for ([k (in-hash-keys board)])
    (solutions-from board dict k empty)))

;; get all the solutions from the whole board & dictionary over 2 chars
(for ([word (in-generator (solutions board the-dictionary))]
      #:when (>= (string-length word) 3))
  (printf "~a\n" word))
