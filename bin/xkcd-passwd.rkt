#! /usr/bin/env racket
#lang racket

(define word-list "/usr/share/dict/words")
(define words 
  (filter
   (λ (x) (and (<= 4 (string-length x) 7)
               (regexp-match #px"^[[:lower:]]+$" x)))
   (file->lines word-list)))

(define how-many 4)
(define separator "-")

(define (random-list-ref l)
  (list-ref l (random (length l))))

(define output
  (with-output-to-string
    (λ ()
       (printf "Easy:\n\t")
       (for ([i (in-range how-many)])
            (display (random-list-ref words))
            (display separator))
       (display (random 10))
       (printf "\n")

       (define chars 
         (string->list "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"))
       (printf "Annoying:\n\t")
       (for ([i (in-range 10)])
            (display (random-list-ref chars)))
       (printf "\n"))))

(if (getenv "TERM")
    (display output)
    (let ()
      (define-values (sp _a stdout _c)
        (subprocess #f #f #f 
                    "/usr/bin/xmessage" "-file" "-"))
      (display output stdout)
      (close-output-port stdout)
      (subprocess-wait sp)))
