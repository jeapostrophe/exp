#lang racket/base
(require racket/file
         net/url
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

(define (word! w)
  (match w
    [(word f #f r e p)
     (list f r "" e p)]
    [(word f us r e p)
     (define x (read-url/cache (string->url us)))

     ;; xxx Idioms and set expressions:
     ;; xxx Related words:
     ;; xxx Verb conjugation:
     ;; xxx Proverbs and sayings:
     ;; xxx Other forms of the word (declensions):
     ;; xxx Example sentences:

     (define mp3s ((sxpath '(// (div (@ (equal? (id "wod_vocab")))) (script 3) *text*)) x))
     (define mp3-us
       (match (regexp-match #rx"soundFile: \"(.*?)\"," (apply string-append mp3s))
         [(list _ mp3)
          mp3]
         [else
          (unless (member f '(83 152 250 282 396 430 568 574))
            (error 'russian "~v ~v ~v"
                   us
                   mp3s
                   ((sxpath '(// (div (@ (equal? (id "wod_vocab")))))) x)))
          #f]))

     (list f r
           (cond
             [mp3-us
              (define u (string->url mp3-us))
              (cache-static-url! u)
              (url->cache-path u)]
             [else
              ""])
           e p)]))

(define (list! us)
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

(define (write-csv l)
  (for ([r (in-list l)])
    (for ([e (in-list r)])
      (display (regexp-replace* #rx"[ \r\n\t]" (srl:sxml->xml e) " "))
      (display #\tab))
    (display #\newline)))

(define word->csv
  (match-lambda
   [(list freq r mp3-url e p)
    (list (number->string freq) 
          r
          (match mp3-url
            [""
             ""]
            [else
             (format "[sound:~a]" mp3-url)])
          `(span (@) . ,e)
          p)]))

(define (root!)
  (define ws
    (append*
     (list! "http://masterrussian.com/vocabulary/most_common_words.htm")
     (for/list ([i (in-range 2 13)])
       ;; xxx 8 is wrong and needs a tr on line 225
       (list! (format "http://masterrussian.com/vocabulary/most_common_words_~a.htm" i)))))

  (define word-db
    (for/list ([w (in-list ws)])
      (word! w)))

  (with-output-to-file
      (build-path *output-dir* "word.csv")
    #:exists 'replace
    (λ ()
      (write-csv (map word->csv word-db))))

  (length word-db))

(module+ main
  (root!))
