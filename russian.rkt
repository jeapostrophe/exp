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

;; //*[@id="wrapper"]/div[2]/div/div/div[1]/div/p[2]/a

(define (root! us)
  (define x (read-url/cache (string->url us)))
  
  (define ns ((sxpath '((p ((equal? (a "Next >")))))) x))
  (error 'root "~v" ns)

  (define ws ((sxpath '(// (table (@ (equal? (class "topwords")))) tr)) x))
  (for/list ([w (in-list (rest ws))])
    (match-define `(tr (@ (class ,_)) (td (@ (class "number")) ,number-s . ,_) (td) (td (@ (class "word")) (a (@ (href ,word-url-s) . ,_) ,word) (& nbsp)) (td ,english) (td ,part))
                  w)
    (list (inexact->exact (string->number number-s)) word-url-s word english part)))

(module+ main
  (root! "http://masterrussian.com/vocabulary/most_common_words.htm"))
