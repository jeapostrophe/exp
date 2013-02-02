#lang racket
(require sxml/html
         net/url
         sxml)

(require racket/pretty)

(define (scrape-archive href)
  (pretty-print
   ((sxpath '(// table // a))
    (call/input-url (string->url href) get-pure-port
                    html->xexp))))

(module+ main
  (define start "http://marathon.speeddemosarchive.com/history")

  (define archives
    ((sxpath '(// p (a (@ (equal? (target "_blank")))) ))
     (call/input-url (string->url start) get-pure-port
                     html->xexp)))

  (for ([a (in-list archives)])
    (define href (first ((sxpath '(// a @ href *text*)) (list '*TOP* a))))
    (define title (first ((sxpath '(// a *text*)) (list '*TOP* a))))
    (printf "~a: ~a\n" title href)
    (scrape-archive href)))
