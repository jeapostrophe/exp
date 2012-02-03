#lang racket
(require racket/package
         net/url
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(package-begin
 (define u "http://www.lds.org/scriptures/bofm/1-ne/1?lang=jpn")
 (define xe (call/input-url (string->url u) get-pure-port html->xexp))
 (define (get-div class)
   (first ((sxpath (format "//div[@class=~s]" class)) xe)))

 #;(pretty-print xe)

 (define subtitle-raw (list-tail (get-div "subtitle") 2))
 (define intro-raw (list-tail (get-div "intro") 2))
 (define summary-raw (rest (first (list-tail (get-div "summary") 2))))
 (define verses-xe (list '*TOP* (get-div "verses")))

 (define (simpl-verse p)
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
    p))

 (define (simpl-verse->expression l)
   (filter-map
    (match-lambda
     [(? string? e)
      e]
     [`(ruby ,kanji)
      kanji]
     [`(ruby (rp "(") (rt ,reading) (rp ")"))
      #f]
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
          (format "「~a」" reading)]
         [`(ruby ,kanji (rp "(") (rt ,reading) (rp ")"))
          (format "~a「~a」" kanji reading)])
        l))
 (define (los->s los)
   (regexp-replace*
    #rx"^ +"
    (regexp-replace* #rx" +$"
                     (regexp-replace* #rx"\u200B" (apply string-append los) "")
                     "")
    ""))

 (define (prep-verse v)
   (list-tail v 2))
 (define (combine-verse sv)
   (define kanji (simpl-verse->expression sv))
   (define reading (simpl-verse->reading sv))
   (cons (los->s kanji)
         (los->s reading)))
 (define clip-verse prep-verse)

 (define parse-verse (compose combine-verse simpl-verse))

 (define subtitle (parse-verse subtitle-raw))
 (define intro (parse-verse intro-raw))
 (define summary (parse-verse summary-raw))
 (define verses (map (compose combine-verse clip-verse simpl-verse prep-verse)
                     ((sxpath "//p") verses-xe)))

 (void))

"http://www.lds.org/scriptures/bofm/1-ne/1?lang=en"

