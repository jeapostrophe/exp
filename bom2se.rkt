#lang racket
(require net/url
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(define u "http://www.lds.org/scriptures/bofm/1-ne/1?lang=jpn")
"http://www.lds.org/scriptures/bofm/1-ne/1?lang=en"

(define xe (call/input-url (string->url u) get-pure-port html->xexp))
(define (get-div class)
  (first ((sxpath (format "//div[@class=~s]" class)) xe)))

#;(pretty-print xe)

(define subtitle (list-tail (get-div "subtitle") 2))
(define intro (list-tail (get-div "intro") 2))
(define summary (rest (first (list-tail (get-div "summary") 2))))
(define verses-xe (list '*TOP* (get-div "verses")))

(define (simpl-verse p)
  (list-tail
   (append-map
    (match-lambda
     [(? string? e)
      (list e)]
     [(and e (list-rest 'ruby _))
      (list e)]
     [(list 'a @s rest ...)
      rest]
     [(list-rest (or 'sup 'span) _)
      empty])
    (list-tail p 2))
   2))

(define (simpl-verse->expression l)
  (map (match-lambda
        [(? string? e)
         e]
        [`(ruby ,kanji)
         kanji]
        [`(ruby (rp "(") (rt ,reading) (rp ")"))
         reading]
        [`(ruby ,kanji (rp "(") (rt ,reading) (rp ")"))
         kanji])
       l))
(define (simpl-verse->reading l)
  (map (match-lambda
        [(? string? e)
         e]
        [`(ruby ,kanji)
         kanji]
        [`(ruby (rp "(") (rt ,reading) (rp ")"))
         reading]
        [`(ruby ,kanji (rp "(") (rt ,reading) (rp ")"))
         (format "~a「~a」" kanji reading)])
       l))

(define verses (map simpl-verse ((sxpath "//p") verses-xe)))
(define kanji-verses (map simpl-verse->expression verses))
(define reading-verses (map simpl-verse->reading verses))

(pretty-print
 reading-verses)
