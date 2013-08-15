#lang racket/base
(require racket/file
         racket/function
         net/url
         racket/string
         racket/match
         racket/port
         racket/list
         sxml
         sxml/html)

(define (read-url/bytes u)
  (define ans
    (call/input-url u get-pure-port
                    port->bytes
                    (list "User-Agent: Mozilla/5.0 (Ubuntu; X11; Linux x86_64; rv:8.0) Gecko/20100101 Firefox/8.0")))
  (when (regexp-match #rx"403 Forbidden" ans)
    (error 'russian "You've been banned. :("))
  ans)

(define *output-dir*
  "/home/jay/Downloads/russian")

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
  (cache-url-to-file! u cache-path)
  cache-path)

(define result-root
  (build-path *output-dir* "results"))
(make-directory* result-root)

(define (read-url/cache u)
  (define p (cache-static-url! u))
  (html->xexp (file->string p)))

(define (parse-number-s number-s)
  (cond
    [(string? number-s)
     (inexact->exact (string->number number-s))]
    [else
     (error 'parse-number-s "~e" number-s)]))

(struct word (freq url word english part) #:transparent)

(define (parse/list us)
  (define x (read-url/cache (string->url us)))
  (define trs ((sxpath '(// (table (@ (equal? (class "topwords")))) tr)) x))
  (define ws
    (for/list ([w (in-list (rest trs))])
      (with-handlers ([exn:fail?
                       (λ (x)
                         (error 'list! "~v: ~a" w (exn-message x)))])
        (match-define
         (list 'tr (list '@ (list 'class _))
               (list 'td (list '@ (list 'class "number"))
                     '(a (@ (name "205") (id "220"))) ...
                     (? string? number-s) '(& nbsp) ...)
               '(td) ...
               (list 'td (list '@ (list 'class "word"))
                     "\r\n" ...
                     (or (and (? string? russian)
                              (app (λ _ #f) word-url-s))
                         (list 'a (list '@ (list 'href word-url-s) _ ...) russian
                               '(a) ...
                               '(& nbsp) ...))
                     '(a) ...
                     '(& nbsp) ...)
               (list-rest 'td english)
               (list 'td part))
         w)
        (word (parse-number-s number-s) word-url-s russian english part))))
  ws)

(define (parse/word word! sentence! w)
  (match w
    [(word f #f r e p)
     (word!
      (list f r "" e p #f))]
    [(word f us r e p)
     (define x (read-url/cache (string->url us)))

     ;; xxx Verb conjugation: [verbs]
     ;; xxx Related words: [words]

     (define mp3s ((sxpath '(// (div (@ (equal? (id "wod_vocab")))) (script 3) *text*)) x))

     (define (parse-mp3-js mp3s)
       (match (regexp-match #rx"soundFile: \"(.*?)\"," (apply string-append mp3s))
         [(list _ mp3)
          mp3]
         [_
          #f]))

     (define mp3-us
       (or (parse-mp3-js mp3s)
           (begin (unless (member f '(83 152 250 282 396 430 568 574))
                    (error 'russian "~v ~v ~v"
                           us
                           mp3s
                           ((sxpath '(// (div (@ (equal? (id "wod_vocab")))))) x)))
                  #f)))

     (define (grab-mp3 mp3-us)
       (cond
         [mp3-us
          (define u (string->url mp3-us))
          (cache-static-url! u)
          (url->cache-path u)]
         [else
          ""]))

     (define cx (rest (rest (first ((sxpath '(// (div (@ (equal? (class "col1")))))) x)))))
     (let loop ([cx cx])
       (unless (empty? cx)
         (match (first cx)
           [`(div (@ (id "wod_header")) . ,kind)
            (match (string-trim (apply string-append (filter string? kind)))
              ["Related words:"
               (eprintf "Unwise to parse related: ~a\n" us)
               (loop (rest cx))]
              [(or "Verb conjugation:"
                   "Other forms of the word (declensions):")
               (eprintf "Hard to parse tables: ~a\n" us)
               (loop (rest cx))]
              ["Idioms and set expressions:"
               (let sloop ([cx (rest cx)])
                 (match (first cx)
                   [`(ul . ,lis)
                    (let sloop2 ([lis lis])
                      (match lis
                        [`((li (b ,r) ,e=) . ,more)
                         (define e (string-trim (second (string-split e= "="))))
                         (sentence! (list r "" e ""))
                         (sloop2 more)]
                        [`((li (b ,r) ,e=1 (b ,e=2) ,e=3 (br) (& nbsp) (span (@ (class "highlight_lit")) (& nbsp) "literal" (& nbsp)) " " (i ,lit)) . ,more)
                         (define e (string-trim (second (string-split (string-append e=1 e=2 e=3) "="))))
                         (sentence! (list r "" e lit))
                         (sloop2 more)]
                        [`((li (b ,r) ,e= (br) (& nbsp) (span (@ (class "highlight_lit")) (& nbsp) "literal" (& nbsp)) " " (i ,lit)) . ,more)
                         (define e (string-trim (second (string-split e= "="))))
                         (sentence! (list r "" e ""))
                         (sloop2 more)]
                        [`()
                         (void)]
                        [x
                         (error 'idioms "~a ~v" us x)]))
                    (loop (rest cx))]
                   [else
                    (sloop (rest cx))]))]
              [(or "Proverbs and sayings:"
                   "Example sentences:")
               (let sloop ([cx (rest cx)])
                 (match (first cx)
                   [`(ul (@ (class "phrase_plain")) . ,lis)
                    (define parse-rpart
                      (match-lambda
                       [(list (? string? s))
                        (values s #f)]
                       [(list _ ...
                              (list 'script (list '@ (list 'type "text/javascript"))
                                    (? string? js) ...)
                              (? string? rs) ...)
                        (values (string-trim (apply string-append rs))
                                (parse-mp3-js js))]
                       [x
                        (error 'rpart "~a ~a ~v" us kind x)]))

                    (let sloop2 ([lis lis])
                      (match lis
                        [`((li (@ (class "first"))) (li) . ,more)
                         (sloop2 more)]
                        [`((li (@ (class "first")) (span (@ (style "color: green; font-size: 10px;font-family:Arial,helvetica;")) "Click on " #\► " to listen to the examples."))
                           . ,more)
                         (sloop2 more)]
                        [`((li (@ (class "first")) . ,rpart)
                           (li ,e)
                           (li (span (@ (class "highlight_lit")) (& nbsp) "literal" (& nbsp)) ,lit)
                           . ,more)
                         (define-values (r rmp3) (parse-rpart rpart))
                         (sentence! (list r (grab-mp3 rmp3)
                                          (string-trim e)
                                          (string-trim lit)))
                         (sloop2 more)]
                        [`((li (@ (class "first")) . ,rpart)
                           (li)
                           (li (span (@ (class "highlight_lit")) (& nbsp) "literal" (& nbsp)) ,lit)
                           . ,more)
                         (define-values (r rmp3) (parse-rpart rpart))
                         (sentence! (list r (grab-mp3 rmp3)
                                          ""
                                          (string-trim lit)))
                         (sloop2 more)]
                        [`((li (@ (class "first")) . ,rpart)
                           (li ,e)
                           . ,more)
                         (define-values (r rmp3) (parse-rpart rpart))
                         (sentence! (list r (grab-mp3 rmp3)
                                          (string-trim e)
                                          ""))
                         (sloop2 more)]
                        [`()
                         (void)]
                        [x
                         (error 'sentences "~a ~v" us x)]))
                    (loop (rest cx))]
                   [else
                    (sloop (rest cx))]))]
              [k
               (error 'word! "unknown kind ~v @ ~a" k us)])]
           [else
            (loop (rest cx))])))

     (word!
      (list f r
            (grab-mp3 mp3-us)
            e p
            us))]))

(define (write-csv l)
  (for ([r (in-list l)])
    (for ([e (in-list r)])
      (display (regexp-replace* #rx"[ \r\n\t]" (srl:sxml->xml e) " "))
      (display #\tab))
    (display #\newline)))

(define word->csv
  (match-lambda
   [(list freq r mp3-url e p us)
    (list r
          (match mp3-url
            [""
             ""]
            [else
             (format "[sound:~a]" mp3-url)])
          `(span (@) . ,e)
          p
          (if freq
            (number->string freq)
            "")
          (if us
            `(a (@ (href ,us)) ,us)
            ""))]))

(define (snoc l x)
  (append l (list x)))

(define (root!)
  (define ws
    (append*
     (parse/list "http://masterrussian.com/vocabulary/most_common_words.htm")
     (for/list ([i (in-range 2 13)])
       ;; xxx 8 is wrong and needs a tr on line 225
       (parse/list (format "http://masterrussian.com/vocabulary/most_common_words_~a.htm" i)))))

  (define-syntax-rule (define-extend! extend! word-db word->csv)
    (begin (define word-db empty)
           (define (extend! l)
             (set! word-db (snoc word-db (word->csv l))))))

  (define-extend! word! word-db word->csv)
  (define-extend! sentence! sentence-db identity)

  (for ([w (in-list ws)])
    (parse/word word! sentence! w))

  (with-output-to-file (build-path *output-dir* "word.csv")
    #:exists 'replace
    (λ () (write-csv word-db)))
  (with-output-to-file (build-path *output-dir* "sentence.csv")
    #:exists 'replace
    (λ () (write-csv sentence-db)))

  (length word-db))

(module+ main
  (root!))
