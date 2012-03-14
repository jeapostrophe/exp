#lang racket/base
(require racket/function
         racket/list
         racket/port
         racket/file
         net/url
         racket/match
         racket/pretty
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(define-syntax-rule (debug e) (void))

(define *output-dir* "/home/jay/Downloads/kdict")
(define *max* 3232)
(define *steps* (ceiling (/ *max* 10)))

(define (step-start step)
  (add1 (* (sub1 step) 10)))

(define (jdict-url start)
  (url "http"
       #f
       "www.saiga-jp.com"
       #f #t
       (list (path/param "cgi-bin" empty)
             (path/param "dic.cgi" empty))
       (list (cons 'm "view")
             (cons 'sc "0")
             (cons 'f "0")
             (cons 'j "")
             (cons 'g "")
             (cons 'e "")
             (cons 's "")
             (cons 'rt "0")
             (cons 'start (number->string start))
             (cons 'sid "1327595084_68489"))
       #f))

;; http://www.saiga-jp.com/cgi-bin/dic.cgi?m=search&sc=0&f=0&j=&g=&e=&s=&rt=0&start=1&sid=1327593805_50151

(define jdict-base (jdict-url 0))

(define (read-url/bytes u)
  (define ans
    (call/input-url u get-pure-port
                    port->bytes
                    (list "Cookie: kanji_dictionary=1327595084_68489:1327595084_68489:1"
                          "User-Agent: Mozilla/5.0 (Ubuntu; X11; Linux x86_64; rv:8.0) Gecko/20100101 Firefox/8.0")))
  (when (regexp-match #rx"403 Forbidden" ans)
        (error 'jdictate "You've been banned. :("))
  ans)

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
(define (parse-example t)
  (define tx (list '*TOP* t))
  (define url (first* ((sxpath '(td a @ href *text*)) tx)))
  (define img? (cons? ((sxpath '(td img)) tx)))
  (define str (first* ((sxpath '(td *text*)) tx)))
  (cond
   [(and url str)
    (list 'example/audio url (regexp-replace* #rx"^ +" str ""))]
   [(and img? str)
    (list 'example (regexp-replace* #rx"^ +" str ""))]
   [str
    (list 'cont str)]
   [else
    #f]))

(define (reflow-examples es)
  (debug (printf "\t\t\t\treflow: ~v\n" es))
  (reverse
   (for/fold
    ([nes empty])
    ([e (in-list es)])
    (match
     e
     [(list-rest (or 'example/audio 'example) _)
      (list* e nes)]
     [(list 'cont str)
      (list* (append (first nes) (list str))
             (rest nes))]))))

(define (parse-step s)
  (define x (html->xexp s))
  #;(pretty-print x)
  (define results (list* '*TOP* (fifth ((sxpath '(// table)) x))))
  (define real-results (list-tail ((sxpath '(table tbody tr)) results) 3))

  (debug (printf "\tgot ~a results\n" (length real-results)))

  (for/list
   ([tr (in-list real-results)]
    [i (in-naturals 1)])
   (define trx (list '*TOP* tr))
   (debug (printf "\t\tresult ~a\n" i))
   
   (debug (pretty-print trx))

   (define-syntax-rule (show f)
     (debug (printf (string-append "\t\t\t" (symbol->string 'f) ": ~v\n") f)))
   (define-syntax-rule (show-define f e)
     (begin (define f e) (show f)))

   (show-define grade
     (string->number (first ((sxpath '(tr (td 1) *text*)) trx))))
   (show-define kanji
     (first ((sxpath '(tr (td 2) font *text*)) trx)))
   (show-define stroke
     (string->number (first ((sxpath '(tr (td 3) *text*)) trx))))
   (show-define stroke-order-url
     (parse-js-call (last ((sxpath '(tr (td 3) (img) @ onclick *text*)) trx))))
   (show-define radical-img-url
     (first* ((sxpath '(tr (td 4) img @ src *text*)) trx)))
   (show-define radical-string
     (and (not radical-img-url)
          (last ((sxpath '(tr (td 4) *text*)) trx))))
   (show-define meanings
     ((sxpath '(tr (td 5) *text*)) trx))
   (show-define readings
     (filter-map parse-reading
                 ((sxpath '(tr (td 6) table tbody tr td)) trx)))
   (show-define examples
     (reflow-examples
      (filter-map parse-example
                  ((sxpath '(tr (td 7) table tbody tr td)) trx))))
   (show-define irregular
     (reflow-examples
      (filter-map parse-example
                  ((sxpath '(tr (td 8) table tbody tr td)) trx))))

   (list 'kanji
         grade kanji stroke stroke-order-url
         radical-img-url radical-string meanings readings
         examples irregular)))

(define (extract-url-paths ks)
  (append-map
   (λ (k)
      (match-define
       (list 'kanji
             grade kanji stroke stroke-order-url
             radical-img-url radical-string meanings readings
             examples irregular)
       k)
      (filter-map identity
                  (list* stroke-order-url
                         radical-img-url
                         (append (map second readings)
                                 (map second examples)
                                 (map second irregular)))))
   ks))
(define (extract-urls ks)
  (for/list
   ([p (in-list (extract-url-paths ks))])
   (combine-url/relative jdict-base p)))

(define last-request-secs-path
  (build-path *output-dir* "last-request-secs.rktd"))
(make-directory* *output-dir*)
(define (read-url/bytes/slow u)
  (define last
    (or (with-handlers ([exn? (λ (x) #f)])
                       (file->value last-request-secs-path))
        ;; We don't know how long it has been since you last made a
        ;; request, or if you've been banned. So, we'll wait a long
        ;; time and try then. (long time = 15 minutes)
        (+ (current-seconds) #;(* 60 15))))
  (sync (alarm-evt (* 1000
                      (+ last
                         ;; Wait between each request
                         60))))
  (begin0 (read-url/bytes u)
          (write-to-file (current-seconds) last-request-secs-path #:exists 'replace)))

(define cache-root
  (build-path *output-dir* "cache"))
(make-directory* cache-root)
(make-directory* (build-path cache-root "static"))

(define result-root
  (build-path *output-dir* "results"))
(make-directory* result-root)

(define (cache-url-to-file! u cache-path)
  (unless
   (file-exists? cache-path)
   (printf "  Caching ~a -> ~a\n" (url->string u) cache-path)
   (define bs (read-url/bytes/slow u))
   (display-to-file bs cache-path #:exists 'replace)))
(define (cache-static-url! u)
  (define cache-path
    (build-path cache-root "static"
                (apply string-append
                       (add-between (map path/param-path (url-path u)) "."))))
  (cache-url-to-file! u cache-path))

;; XXX There may be some duplication since I can't get steps above 100
;; without filtering by grades above 6

(define (path->number p)
  (define n (string->number (regexp-replace* #rx".html$" (path->string p) "")))
  (unless (number? n)
    (error 'path->number "~v" p))
  n)

(define (directory-files p)
  (for/list ([f (in-list (directory-list p))]
             #:when (file-exists? f))
    f))

(parameterize ([current-directory cache-root])
  (for ([p (in-list (sort (directory-files cache-root) <= #:key path->number))])
    (debug (printf "~a\n" p))
    (define result-path
      (build-path result-root (path-replace-suffix p #"rktd")))
    (unless (file-exists? result-path)
      (define s (file->string p))
      (define res (parse-step s))
      (write-to-file res result-path #:exists 'replace))
    (define res (file->value result-path))
    (for-each cache-static-url! (extract-urls res))))

#;
(for ([step (in-range 1 (add1 *steps*))])
     (printf "Step ~a\n" step)
     (define u (jdict-url (step-start step)))
     (define cache-path
       (build-path cache-root (format "~a.html" step)))
     (define result-path
       (build-path result-root (format "~a.rktd" step)))
     ;; XXX Can't get this step to work. I think it is looking at a
     ;; cookie or something like that
     #;(cache-url-to-file! u cache-path)
     ;; XXX Not sure if the parser is robust enough yet
     (when (file-exists? cache-path)
       (define s (file->string cache-path))
           (define res (parse-step s))
           (write-to-file res result-path #:exists 'replace)
           ;; XXX I want to get the metadata before getting the static
           ;; content; since I need to wait anyways, these can wait.
           (for-each cache-static-url! (extract-urls res))))
