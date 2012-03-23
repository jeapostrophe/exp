#lang racket/base
(require racket/function
         racket/list
         racket/port
         racket/file
         xml
         net/url
         racket/match
         racket/pretty
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(struct reading (sound-url reading-str) #:prefab)
(struct example/audio (sound-url expression) #:prefab)
(struct example-cont (expression) #:prefab)
(define example-url
  (match-lambda
   [(example/audio url _)
    url]
   [_ #f]))
(struct kanji (grade char stroke stroke-order-url radical-img-url radical-string meanings readings examples irregular) #:prefab)

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
       (reading url (regexp-replace* #rx"^ +" str ""))))
(define (parse-example t)
  #;(pretty-print t)
  (define tx (list '*TOP* t))
  (define url (first* ((sxpath '(td a @ href *text*)) tx)))
  (define img? (cons? ((sxpath '(td img)) tx)))
  (define str (first* ((sxpath '(td *text*)) tx)))
  #;(printf "~v\n" (list url img? str))
  (cond
    [(and url str)
     (example/audio url (regexp-replace* #rx"^ +" str ""))]
    [(and img? str)
     (example-cont (regexp-replace* #rx"^ +" str ""))]
    [str
     (example-cont str)]
    [else
     #f]))

(define (reflow-examples es)
  #;(printf "reflow\n")
  (debug (printf "\t\t\t\treflow: ~v\n" es))
  (reverse
   (for/fold
       ([nes empty])
       ([e (in-list es)])
     (match e
       [(? example/audio?)
        (list* e nes)]
       [(example-cont str)
        (if (empty? nes)
          empty
          (list*
           (struct-copy
            example/audio (first nes)
            [expression
             (string-append
              (example/audio-expression (first nes))
              str)])
           (rest nes)))]))))

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
    (show-define char
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

    (kanji
     grade char stroke stroke-order-url
     radical-img-url radical-string meanings readings
     examples irregular)))

(define (extract-url-paths ks)
  (append-map
   (λ (k)
     (match k
       [(kanji grade char stroke stroke-order-url radical-img-url
               radical-string meanings readings examples irregular)
        (kanji
         grade char stroke stroke-order-url
         radical-img-url radical-string meanings readings
         examples irregular)
        (filter-map identity
                    (list* stroke-order-url
                           radical-img-url
                           (append (map reading-sound-url readings)
                                   (filter-map example-url examples)
                                   (map example-url irregular))))]
       [_
        (pretty-print k)
        (error 'bad)]))
   ks))
(define (extract-urls ks)
  (for/list
      ([p (in-list (extract-url-paths ks))])
    (complete-jdict-url p)))

(define (complete-jdict-url p)
  (combine-url/relative jdict-base p))

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
                         10))))
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
(define (url->cache-path u)
  (apply string-append
         (add-between (map path/param-path (url-path u)) ".")))
(define (cache-static-url! u)
  (define cache-path
    (build-path cache-root "static"
                (url->cache-path u)))
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

(define results
  (apply
   append
   (parameterize ([current-directory cache-root])
     (define ps
       (sort (directory-files cache-root) <= #:key path->number))
     (for/list ([p (in-list ps)]
                [i (in-naturals 1)])
       #;(printf "~a (~a/~a)\n" p i (length ps))
       (define result-path
         (build-path result-root (path-replace-suffix p #"rktd")))
       (unless (file-exists? result-path)
         (define s (file->string p))
         (define res (parse-step s))
         (write-to-file res result-path #:exists 'replace))
       (define res (file->value result-path))
       (for-each cache-static-url! (extract-urls res))
       res))))

(define all-kanji (remove-duplicates results))

(printf "Pruned ~a down to ~a\n"
        (length results)
        (length all-kanji))

(define (kanji<=? a b)
  (define a_g (kanji-stroke a))
  (define b_g (kanji-stroke b))
  (if (= a_g b_g)
    (<= (kanji-grade a)
        (kanji-grade b))
    (<= a_g b_g)))

(define sorted-kanji
  (sort all-kanji kanji<=?))

(define (kanji-url->path p)
  (if p
    (url->cache-path (complete-jdict-url p))
    ""))

(define (wrap kind url)
  (if (string=? url "")
    ""
    (match kind
      ['img
       `(img ([src ,url]))]
      ['sound
       (format "[sound:~a]" url)])))
(define reading->xexpr
  (match-lambda
   [(reading url string)
    `(span ,(wrap 'sound (kanji-url->path url)) nbsp ,string)]))

(define kanji->csv-row
  (match-lambda
   [(kanji grade char stroke stroke-order-url radical-img-url radical-string meanings readings examples irregular)
    (list (number->string grade)
          char
          (number->string stroke)
          (wrap 'img (kanji-url->path stroke-order-url))
          (wrap 'img (kanji-url->path radical-img-url))
          (or radical-string "N/A")
          `(p ,@(add-between meanings '(br)))
          `(p ,@(add-between (map reading->xexpr readings) '(br))))]))

(define (write-csv l)
  (for ([r (in-list l)])
    (for ([e (in-list r)])
      (display (xexpr->string e))
      (display #\tab))
    (display #\newline)))

(with-output-to-file
    (build-path *output-dir* "kanji.csv")
  #:exists 'replace
  (λ ()
    (write-csv
     (list* (list "Grade"
                  "Kanji"
                  "Strokes"
                  "Stroke Order"
                  "Radical Image"
                  "Radical String"
                  "Meanings"
                  "Readings")
            (map kanji->csv-row
                 sorted-kanji)))))

(define all-examples
  (append-map (λ (k) (append (kanji-examples k) (kanji-irregular k)))
              sorted-kanji))

(define example->csv-row
  (match-lambda
   [(example/audio url (regexp #rx"^(.*?)（(.*?)） / (.*?)$"
                               (list _ expression reading meaning)))
    (list expression (wrap 'sound url) reading meaning)]))

(with-output-to-file
    (build-path *output-dir* "examples.csv")
  #:exists 'replace
  (λ ()
    (write-csv
     (list*
      (list "Expression" "Sound" "Reading" "Meaning")
      (map example->csv-row
          all-examples)))))
