#lang racket
(require net/url
         racket/pretty
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(define (table-display l)
  (define how-many-cols (length (first l)))
  (define max-widths
    (for/list ([col (in-range how-many-cols)])
      (apply max (map (compose string-length (curryr list-ref col)) l))))
  (for ([row (in-list l)])
    (for ([col (in-list row)]
          [i (in-naturals 1)]
          [width (in-list max-widths)])
      (printf "~a~a"
              col
              (if (= i how-many-cols)
                ""
                (make-string (+ (- width (string-length col)) 4) #\space))))
    (printf "\n")))

(module+ main
  (define u "http://www.mygranturismo.net/eventlist.php")
  (define x (call/input-url (string->url u) get-pure-port html->xexp))

  (define-values
    (evts cat)
    (for/fold ([evts empty]
               [cat #f])
        ([r (in-list (rest ((sxpath "//tr") x)))])
      (define rx (list '*TOP* r))
      (match*
          [((sxpath "/tr/@class/text()") rx)
           ((sxpath "/tr/td[1]/@class/text()") rx)]
        [((list (regexp #rx"^cl ")) _)
         (define lvl (first ((sxpath "/tr/td[1]/text()") rx)))
         (define evt (first ((sxpath "/tr/td[2]/text()") rx)))
         (values (cons (list lvl cat evt) evts)
                 cat)]
        [((list) (list (or "bg_fondgris" "bspec")))
         (values evts
                 cat)]
        [((list) (list "e_ong"))
         (values evts
                 (first ((sxpath "/tr/td[1]/text()") rx)))]
        [(x y)
         (error "failed on ~e" r)])))

  (table-display 
   (sort evts <= #:key (compose string->number first))))
