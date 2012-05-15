#lang racket/base
(require racket/match
         racket/list)

(define empty-dict (hasheq))
(define empty-entry (cons #f empty-dict))
(define (dict-add d w)
  (if (empty? w)
    d
    (hash-update d (first w)
                 (match-lambda
                  [(cons word? rest-d)
                   (cons (or word? (empty? (rest w)))
                         (dict-add rest-d (rest w)))])
                 empty-entry)))
(define (dict-add* d s)
  (dict-add d (string->list s)))

(define dict-pth "/usr/share/dict/words")
(define the-dictionary
  (for/fold ([d empty-dict])
      ([w (in-lines (open-input-file dict-pth))])
    (dict-add* d w)))

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

(define (solutions-from board dict k path)
  (define c (hash-ref board k #f))
  (when c
    (match-define (cons word? new-dict)
                  (hash-ref dict c empty-entry))
    (define new-path (cons c path))
    (when word?
      (void (list->string (reverse new-path))))
    (unless (zero? (hash-count new-dict))
      (define new-board (hash-remove board k))
      (match-define (cons row col) k)
      (for* ([drow (in-list '(-1 0 1))]
             [dcol (in-list '(-1 0 1))])
        (solutions-from new-board new-dict
                        (cons (+ row drow)
                              (+ col dcol))
                        new-path)))))

(time
 (for ([k (in-hash-keys board)])
   (solutions-from board the-dictionary k empty)))
