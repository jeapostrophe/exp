#lang racket/base
(require racket/match
         racket/list)

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

(define dict-pth "/usr/share/dict/words")
(define the-dictionary
  (for/fold ([d empty-dict])
      ([w (in-lines (open-input-file dict-pth))])
    (dict-add d (string->list w))))

(define board-n 4)
(define letters
  (string->list "abcdefghijklmnopqrstuvwxyz"))
(define (random-list-ref l)
  (list-ref l (random (length l))))
(define board
  (for*/fold ([cell->char (hash)])
      ([row (in-range board-n)]
       [col (in-range board-n)])
    (hash-set cell->char (cons row col)
              (random-list-ref letters))))

(for ([row (in-range board-n)])
  (for ([col (in-range board-n)])
    (printf "~a" (hash-ref board (cons row col))))
  (printf "\n"))
(printf "\n")

(define (solutions-from board dict k prefix)
  (define c (hash-ref board k #f))
  (when c
    (match-define (cons word? next-dict)
                  (hash-ref dict c empty-entry))
    (define next-prefix (cons c prefix))
    (when word?
      (displayln (list->string (reverse next-prefix))))
    (unless (zero? (hash-count next-dict))
      (define next-board (hash-remove board k))
      (match-define (cons row col) k)
      (for* ([drow (in-list '(-1 0 1))]
             [dcol (in-list '(-1 0 1))])
        (solutions-from next-board next-dict
                        (cons (+ row drow)
                              (+ col dcol))
                        next-prefix)))))

(for ([k (in-hash-keys board)])
  (solutions-from board the-dictionary k empty))
