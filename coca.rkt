#lang racket/base
(require racket/match
         racket/list
         sxml
         sxml/html)

(define POS
  (hash
   "a" "article"
   "v" "verb"
   "c" "conjunction"
   "i" "preposition"
   "t" "infinitive marker"
   "p" "pronoun"
   "d" "determiner"
   "x" "???"
   "r" "adverb"
   "m" "number"
   "n" "noun"
   "e" "existential there"
   "j" "adjective"
   "u" "interjection"))

(define (parse p)
  (define x (call-with-input-file p html->xexp))
  (define trs ((sxpath '(// (table (@ (equal? (id "table1")))
                                   (@ (equal? (border "1"))))
                            tr))
               x))
  (printf "Found ~a\n" (length trs))
  (for ([i (in-naturals)]
        [tr (in-list (rest (rest trs)))])
    (match tr
      [`(tr "\r\n" (td (@ (align "center")) ,rank) "\r\n" (td (& nbsp) (& nbsp) (& nbsp) ,word) "\r\n" (td (@ (align "center")) ,pos) . ,_)
       (printf "~a\t~a\t~a\n" rank word (hash-ref POS pos (λ () (error 'coca "Missing pos ~v for ~v" pos word))))]
      [_
       (error 'coca "Failed on row ~a, ~e" i tr)])))

(module+ main
  (parse (build-path (find-system-path 'home-dir)
                     "Downloads"
                     "COCA-5000.html")))
