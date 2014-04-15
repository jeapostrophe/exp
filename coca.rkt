#lang racket/base
(require racket/match
         racket/list
         sxml
         sxml/html)

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
      [`(tr "\r\n" (td (@ (align "center")) ,rank) "\r\n" (td (& nbsp) (& nbsp) (& nbsp) ,word) "\r\n" (td (@ (align "center")) ,pos) "\r\n" (td (@ (align "center")) ,freq) "\r\n" (td (@ (align "center")) ,dispersion) "\r\n")
       (printf "~a. ~a (~a)\n" rank word pos)]
      [_
       (error 'coca "Failed on row ~a, ~e" i tr)])))

(module+ main
  (parse (build-path (find-system-path 'home-dir)
                     "Downloads"
                     "COCA-5000.html")))
