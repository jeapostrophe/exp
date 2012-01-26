#lang racket/base
(require racket/list
         racket/port
         racket/file
         net/url
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(define *output-dir* "/tmp/kdict")
(define (jdict-url start)
  (url "http" 
       #f
       "www.saiga-jp.com"
       #f #t
       (list (path/param "cgi-bin" empty)
             (path/param "dic.cgi" empty))
       (list (cons 'm "view")             
             (cons 'start (number->string start)))
       #f))

(define (parse u)
  (display
   (call/input-url u get-pure-port
                   port->string
                   (list (format "Referer: ~a" (url->string u))))))

#;(parse (jdict-url 0))

(define x (html->xexp (file->string "/tmp/kdict/ex.html")))
(define results (list* '*TOP* (fifth ((sxpath '(// table)) x))))
(define real-results (list-tail ((sxpath '(table tbody tr)) results) 3))

(define (parse-js-call s)
  (second (regexp-match #rx"^[^(]+\\('([^']+)',.+\\);$" s)))
(define (first* x)
  (and (cons? x)
       (first x)))
(define (parse-reading t)
  (define tx (list '*TOP* t))
  (define url (first* ((sxpath '(td a @ href *text*)) tx)))
  (define str (first* ((sxpath '(td *text*)) tx)))
  (and url str
       (list 'reading url (regexp-replace* #rx"^ +" str ""))))

(require racket/pretty)
(for ([tr (in-list real-results)]
      [i (in-range 1)])
     (define trx (list '*TOP* tr))
     (pretty-print trx)
     
     (define grade
       (string->number (first ((sxpath '(tr (td 1) *text*)) trx))))
     (define kanji 
       (first ((sxpath '(tr (td 2) font *text*)) trx)))
     (define stroke
       (string->number (first ((sxpath '(tr (td 3) *text*)) trx))))
     (define stroke-order-url
       (parse-js-call (first ((sxpath '(tr (td 3) (img 2) @ onclick *text*)) trx))))
     (define radical-img-url
       (first ((sxpath '(tr (td 4) img @ src *text*)) trx)))
     (define meanings
       ((sxpath '(tr (td 5) *text*)) trx))
     (define readings
       (filter-map parse-reading
                   ((sxpath '(tr (td 6) table tbody tr td)) trx)))
     (define examples
       ((sxpath '(tr (td 7) table tbody tr td)) trx))
     (define irregular #f)

     (pretty-print (list grade kanji stroke stroke-order-url
                         radical-img-url meanings readings
                         examples irregular)))

