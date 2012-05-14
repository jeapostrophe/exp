#lang racket
(require rackunit
         racket/runtime-path
         (only-in srfi/13 string-reverse))

(define-runtime-path dict-pth "/usr/share/dict/words")
(define dictionary
  (with-input-from-file dict-pth
    (λ ()
      (for/fold ([d (set)])
          ([w (in-lines)])
        (set-add d w)))))

(define letters
  (string->list
   "abcdefghijklmnopqrstuvwxyz"))

(define board-n 6)
(define board
  (for/list ([row (in-range board-n)])
    (begin0
      (for/list ([col (in-range board-n)])
        (define c (list-ref letters (random (length letters))))
        (printf "~a" c)
        c)
      (printf "\n"))))

(define (in-possibilities board)
  (define size (length board))
  (if (zero? size)
    empty
    (append
     ;; all rows
     (map list->string board)
     ;; all cols
     (for/list ([col (in-range size)])
       (list->string
        (map (λ (row)
               (list-ref row col))
             board)))
     ;; all diagonals
     (list
      (list->string
       (for/list ([i (in-range size)])
         (list-ref (list-ref board i) i)))
      (list->string
       (for/list ([i (in-range size)])
         (list-ref (list-ref board (- (sub1 size) i)) i))))
     ;; all possibilites for smaller boards
     (append-map
      in-possibilities
      (list
     ;;; upper left
       (for/list ([row (in-range 0 (- size 1))])
         (for/list ([col (in-range 0 (- size 1))])
           (list-ref (list-ref board row) col)))
     ;;; upper right
       (for/list ([row (in-range 0 (- size 1))])
         (for/list ([col (in-range 1 size)])
           (list-ref (list-ref board row) col)))

     ;;; lower left
       (for/list ([row (in-range 1 size)])
         (for/list ([col (in-range 0 (- size 1))])
           (list-ref (list-ref board row) col)))
     ;;; lower right
       (for/list ([row (in-range 1 size)])
         (for/list ([col (in-range 1 size)])
           (list-ref (list-ref board row) col))))))))

(remove-duplicates
 (filter (λ (possible)
           (and (>= (string-length possible) 3)
                (set-member? dictionary possible)))
         (append-map
          (λ (possible)
            (list possible
                  (string-reverse possible)))
          (in-possibilities board))))
