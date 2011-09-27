#lang racket
(require racket/generator)

;; generate all combinations of strings of length n of characters A-Z

(define start (char->integer #\a))
(define end (char->integer #\z))

(define seq-of-1
  (for/list ([i (in-range start (add1 end))])
            (list i)))

;; seq (list) -> seq (list)
(define (seq-of-n-to-seq-of-add1n s-of-s)
  (for/fold
      ([more empty])
      ([str s-of-s])
    (append more
            (for/list ([ext (extend str)])
                      ext))))

(define (extend str)
   (for/list ([i (in-range start (add1 end))])
       (cons i str)))

(define (show s)
  (for/list ([l s])
            (list->string (map integer->char l))))

(show seq-of-1)

(show (seq-of-n-to-seq-of-add1n (list empty)))

(show (seq-of-n-to-seq-of-add1n
       (seq-of-n-to-seq-of-add1n
                                 (list empty))))

(define all-of-them
  (in-generator
   (let loop ([orig (list empty)])
     (define l-o-l
       (seq-of-n-to-seq-of-add1n orig))

     (for ([str l-o-l])
          (yield str))
     
     (loop l-o-l))))

(for ([s all-of-them]
      [i (in-range 20000)])
     (printf "~a: ~a\n" i (list->string (map integer->char s))))
