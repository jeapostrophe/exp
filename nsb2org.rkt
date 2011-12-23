#lang racket
(require racket/pretty
         (planet "html-parsing.rkt" ("neil" "html-parsing.plt")))

(define p "/home/jay/Dev/scm/github.jeapostrophe/home/etc/bookmarks_12_20_11.html")
(define s (file->string p))
(define x (html->xexp s))
(define l (list-ref x 11))

(define current-indent 1)
(define-syntax-rule (indent e ...)
  (dynamic-wind 
      (lambda () (set! current-indent (add1 current-indent)))
      (lambda () e ...)
      (lambda () (set! current-indent (sub1 current-indent)))))
(define (iprintf . args)
  (for ([i (in-range current-indent)])
       (display "*"))
  (display " ")
  (apply printf args))

(define convert
  (match-lambda
   [`(dl ,_ ,entries ...)
    (for-each convert entries)]
   [`(dt (h3 ,_ ,name) ,_ ,_ ,entries ...)
    (iprintf "~a\n" name)
    (indent
     (for-each convert entries))]
   [`(dt (a (@ (href ,link) . ,_) ,text) . ,_)
    (iprintf "[[~a][~a]]\n" link text)]
   [`(p "\r\n" . ,_)
    (void)]
   [x
    (printf "Error:\n")
    (pretty-print x)
    (exit 1)]))

(convert l)
