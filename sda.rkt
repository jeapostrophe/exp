#lang racket
(require sxml/html
         net/url
         sxml
         xml)

(define (scrape-archive year href)
  (define videos
    ((sxpath '(// table // a))
     (call/input-url (string->url href) get-pure-port
                     html->xexp)))
  (for/list ([v (in-list videos)])
    (define-values (href title) (a->href*title v))
    (cons (format "~a - ~a" year title)
          href)))

(define (a->href*title a)
  (define href (first ((sxpath '(// a @ href *text*)) (list '*TOP* a))))
  (define title (first ((sxpath '(// a *text*)) (list '*TOP* a))))
  (values (regexp-replace #rx"\n" href "") title))

(define (index->time i)
    (define year (+ 2000 i))
    (define month "01")
    (define day "01")
    (format "~a-~a-~aT00:00:00-00:00"
            year month day))

(module+ main
  (require racket/cmdline)

  (define start "http://marathon.speeddemosarchive.com/history")
  (define output-path
    (command-line #:program "sda" #:args (p) p))

  (define years
    ((sxpath '(// p (a (@ (equal? (target "_blank")))) ))
     (call/input-url (string->url start) get-pure-port
                     html->xexp)))

  (define videos
    (append-map
     (λ (a)
       (define-values (href title) (a->href*title a))
       (scrape-archive title href))
     years))  

  (with-output-to-file output-path
    #:exists 'replace
    (λ ()
      (write-xexpr
       `(feed
         ([xmlns "http://www.w3.org/2005/Atom"])
         (title ,(cdata #f #f
                        (format "<![CDATA[~a]]>" "Speed Demos Archive")))
         ;; (link ([href ,(format "~a/atom.xml" *BLOG-URL*)]
         ;;        [rel "self"]))
         ;; (link ([href ,(format "~a/" start)]))
         (updated ,(index->time (length videos)))
         (id ,(format "~a/" start))
         ,@(for/list ([p (in-list videos)]
                      [i (in-naturals)])
             (match-define (cons title href) p)
             `(entry
               (title ([type "html"])
                      ,(cdata #f #f (format "<![CDATA[~a]]>" title)))
               (link ([href
                       ,href]))
               (updated ,(index->time i))
               (id ,href)
               (content
                ([type "html"])
                ,(cdata #f #f
                        (format "<![CDATA[~a]]>"
                                (xexpr->string
                                 `(p "The archive is at: "
                                     (a ([href ,href]) ,href) "."))))))))))))
