#!/usr/bin/env racket
#lang racket/base
(require racket/runtime-path
         racket/match
         racket/list
         racket/format
         racket/port
         racket/system
         racket/date
         racket/string
         racket/file
         xml
         web-server/servlet
         web-server/http
         unstable/socket)

;; xxx touch --time=mtime -r SRC -d DIFF DEST

;; xxx embed videos rather than VLC?

(define-runtime-path y.css "../y.css")

(define VLC-SOCK-PATH "/tmp/vlc.sock")

(define (vlc-rc! rc-cmd)
  (define-values (FROM-VLC TO-VLC)
    (unix-socket-connect VLC-SOCK-PATH))
  (eprintf "Sending ~v to VLC\n" rc-cmd)
  (fprintf TO-VLC "~a\r\n" rc-cmd)
  (fprintf TO-VLC "~a\r\n" "logout")
  (flush-output TO-VLC)
  (close-output-port TO-VLC)
  (define out (port->string FROM-VLC))
  (close-input-port FROM-VLC)
  (eprintf "Read ~v from VLC\n" out)
  out)

(define (vlc-playing?)
  (equal? "1\r\n" (vlc-rc! "is_playing")))
(define (vlc-clear!)
  (vlc-rc! "clear"))
(define (vlc-stop!)
  (vlc-rc! "stop"))
(define (vlc-add! f)
  (vlc-rc! (format "add ~a" f)))
(define (vlc-seek! s)
  (vlc-rc! (format "seek ~a" s)))
(define (vlc-play!)
  (vlc-rc! "play"))
(define (read-num ip)
  (define v (read ip))
  (if (number? v)
      v
      #f))
(define (vlc-current-length)
  (read-num (open-input-string (vlc-rc! "get_length"))))
(define (vlc-current-time)
  (read-num (open-input-string (vlc-rc! "get_time"))))

(define FFPROBE-PATH
  (find-executable-path "ffprobe"))
(define HOME (find-system-path 'home-dir))

;; xxx generalize from URL?
;; xxx recursive showing
;; xxx polite vs impolite
(define ROOT (build-path HOME "Downloads" "YouTube"))
(define DB (build-path ROOT ".db"))

(define (ffprobe p)
  (define-values (sp o i e)
    (subprocess #f #f #f FFPROBE-PATH "-show_format" p))
  (subprocess-wait sp)
  (define duration-s
    (for/or ([x (in-list (port->lines o))])
      (regexp-match #rx"^duration=(.*?)$" x)))
  (close-input-port o)
  (close-input-port e)
  (close-output-port i)
  (or (and duration-s
           (string->number
            (second
             duration-s)))
      0))

(define (regexp-remove rxs s)
  (if (empty? rxs)
      s
      (regexp-remove
       (rest rxs)
       (regexp-replace (first rxs) s ""))))

(struct yf (status name path mtime len-mtime len prog) #:mutable #:prefab)

(define THE-DB (make-hash))
(define (load-db!)
  (when (file-exists? DB)
    (for ([(k v) (in-hash (file->value DB))])
      (hash-set! THE-DB k v))))
(load-db!)
(define (dump-db!)
  (write-to-file THE-DB DB #:exists 'replace))

(define (y-files-raw)
  ;; Add files from disk
  (let ()
    (define ps
      (filter (λ (x) (and (not (equal? ".db" x))
                          (not (equal? ".DS_Store" x))))
              (map path->string (directory-list ROOT))))
    (define fs
      (parameterize ([current-directory ROOT])
        (filter file-exists? ps)))
    (for ([pp (in-list fs)])
      (unless (hash-has-key? THE-DB pp)
        (define p (build-path ROOT pp))
        (define f pp)
        (define msecs (file-or-directory-modify-seconds p))
        (hash-set! THE-DB
                   pp
                   (yf (cond
                        [(regexp-match #rx".part$" f)
                         'P]
                        [else
                         (string->symbol (string (string-ref f 0)))])
                       (substring f 1)
                       (path->string p)
                       msecs
                       0
                       0
                       0)))))
  ;; Remove files not on disk
  (let ()
    (for ([pp (in-list (hash-keys THE-DB))])
      (unless (file-exists? (build-path ROOT pp))
        (hash-remove! THE-DB pp))))
  ;; Update lens from disk
  (let ()
    (for ([(pp a-yf) (in-hash THE-DB)])
      (define p (yf-path a-yf))
      (define msecs (file-or-directory-modify-seconds p))
      (define old-len-time (yf-len-mtime a-yf))
      (unless (and (not (= (yf-len a-yf) 0))
                   (= msecs old-len-time))
        (define new-len (ffprobe p))
        (set-yf-mtime! a-yf msecs)
        (set-yf-len-mtime! a-yf msecs)
        (set-yf-len! a-yf new-len))))
  (dump-db!)
  (hash-values THE-DB))

(define (yf-dname a-yf)
  (regexp-remove (list #rx".part$" #rx".mp4$")
                 (yf-name a-yf)))
(define (yf-dshow a-yf)
  (first (string-split (yf-dname a-yf) " - ")))
(define (yf-dtitle a-yf)
  (string-append* (add-between (rest (string-split (yf-dname a-yf) " - ")) " - ")))
(define (yf-equal? x y)
  (equal? (yf-name x) (yf-name y)))
(define (yf-played? a-yf)
  (member (yf-status a-yf) '(R S)))
(define (yf-unplayed? a-yf)
  (eq? 'U (yf-status a-yf)))
(define (yf-mdates a-yf)
  (parameterize ([date-display-format 'iso-8601])
    (date->string (seconds->date (yf-mtime a-yf)))))
(define (len->lens len)
  (define MINUTES 60)
  (define   HOURS (* 60 MINUTES))
  (define L (inexact->exact (floor len)))
  (define-values (H HR) (quotient/remainder L HOURS))
  (define-values (M S) (quotient/remainder HR MINUTES))
  (~a (~a #:width 2 #:pad-string "0" #:align 'right H) ":"
      (~a #:width 2 #:pad-string "0" #:align 'right M) ":"
      (~a #:width 2 #:pad-string "0" #:align 'right S)))
(define (yf-lens a-yf)
  (len->lens (yf-len a-yf)))
(define (yf-progs a-yf)
  (len->lens (yf-prog a-yf)))

(define (make-y-http)
  (define current-vlc-lock (make-semaphore 1))
  (define current-vlc-yf #f)
  (define continuous? #f)
  (define sort-style 'show)
  (define (is-current-vlc-yf? f)
    (and current-vlc-yf
         (yf-equal? current-vlc-yf f)))

  (define (set-sort-style! s)
    (set! sort-style s))

  (define (y-files-all)
    (sort (y-files-raw)
          (match sort-style
            ['date <=]
            ['time <=]
            ['show
             (λ (x y)
               (if (string=? (yf-dshow x) (yf-dshow y))
                   (<= (yf-mtime x) (yf-mtime y))
                   (string-ci<=? (yf-dshow x) (yf-dshow y))))])
          #:key
          (match sort-style
            ['date yf-mtime]
            ['time yf-len]
            ['show (λ (x) x)])))
  (define (y-files-unplayed)
    (filter yf-unplayed? (y-files-all)))

  (define (play! f)
    (unless (vlc-playing?)
      (when (semaphore-try-wait? current-vlc-lock)
        (set! current-vlc-yf f)
        (printf "Starting VLC on ~a\n" (yf-name f))
        (vlc-clear!)
        (vlc-add! (yf-path f))
        (vlc-seek! (yf-prog f))
        (vlc-play!)
        (thread
         (λ ()
           (printf "Waiting on VLC\n")
           (define len
             (let loop ()
               (define l (vlc-current-length))
               (if (or (not l) (zero? l))
                   (loop)
                   l)))
           (let loop ()
             (define t (vlc-current-time))
             (when t
               (set-yf-prog! f t)
               (dump-db!)
               (unless (= len t)
                 (sleep 1)
                 (loop))))
           (printf "VLC Done\n")
           (vlc-stop!)
           (vlc-clear!)
           (set! current-vlc-yf #f)
           (semaphore-post current-vlc-lock)
           (when (= len (yf-prog f))
             (with-handlers ([exn:fail? void])
               (mark! f 'R))
             (when continuous?
               (play-next! f))))))))
  (define (play-next! f)
    (printf "Continuous play...\n")
    (define fs (y-files-all))
    (define f-and (member f fs yf-equal?))
    (when f-and
      (define f-and-un (filter yf-unplayed? (rest f-and)))
      (unless (empty? f-and-un)
        (play! (first f-and-un)))))

  (define (clean!)
    (for ([f (in-list (y-files-all))]
          #:when (eq? 'R (yf-status f)))
      (delete-file (yf-path f))))
  (define (mark! f s)
    (unless (is-current-vlc-yf? f)
      (printf "Marking ~a as ~a\n" (yf-name f) s)
      (define old (yf-path f))
      (define n (yf-name f))
      (define new
        (build-path ROOT
                    (string-append (symbol->string s) n)))
      (rename-file-or-directory old new)))
  (define (toggle-continuous?!)
    (set! continuous? (not continuous?)))
  (define (restart!)
    (unless current-vlc-yf
      (local-require mzlib/os)
      (system (format "kill -9 ~a" (getpid)))))

  (define (y-http req)
    (send/suspend/dispatch
     ;; xxx use dispatch
     (λ (embed/url)
       (define (do f . args)
         (embed/url
          (λ (req)
            (apply f args)
            (redirect-to "/"))))
       (define yfs (y-files-all))
       (response/xexpr
        #:preamble #"<!DOCTYPE html>"
        `(html
          (head (title ,(format "y (~a of ~a)"
                                (count yf-unplayed? yfs)
                                (length yfs)))
                (style ,(cdata #f #f (file->string y.css))))
          (body
           (div
            ([id "header"])
            (span ([class "date"])
                  ,(date->string (current-date) #t) ":")
            (span
             ,(if current-vlc-yf
                  `(a ([href "#playing"]) "playing")
                  ""))
            (span
             (a
              ([href ,(do toggle-continuous?!)]
               [class ,(format "continuous_~a"
                               (if continuous?
                                   "on" "off"))])
              "continuous"))
            (span
             (a ([href ,(do clean!)]) "clean"))
            (span
             (a ([href ,(do restart!)]) "restart")))
           (table
            ([id "playlist"])
            (thead
             (tr (th ,(if (eq? sort-style 'date)
                          `(span ([class "sort_selected"]) "Date")
                          `(a ([href ,(do set-sort-style! 'date)]) "Date")))
                 (th ,(if (eq? sort-style 'show)
                          `(span ([class "sort_selected"]) "Show")
                          `(a ([href ,(do set-sort-style! 'show)]) "Show")))
                 (th "Title")
                 (th nbsp)
                 (th nbsp)
                 (th ,(if (eq? sort-style 'time)
                          `(span ([class "sort_selected"]) "Length")
                          `(a ([href ,(do set-sort-style! 'time)]) "Length")))
                 (th nbsp)))
            (tbody
             ,@(for/list ([f (in-list yfs)])
                 `(tr ([id ,(if (is-current-vlc-yf? f)
                                "playing"
                                "")]
                       [class ,(format "item status_~a" (yf-status f))])
                   (td
                    ,(symbol->string (yf-status f)) nbsp
                    ,(yf-mdates f))
                   (td ,(yf-dshow f))
                   (td
                    ,(if (eq? 'P (yf-status f))
                         `,(yf-dtitle f)
                         `(a ([href ,(do play! f)])
                           ,(yf-dtitle f))))
                   (td ,(if (zero? (yf-prog f)) "" (yf-progs f)))
                   (td ,(if (zero? (yf-prog f)) "" "/"))
                   (td ,(yf-lens f))
                   (td
                    ,@(let ()
                        (define menu
                          (match (yf-status f)
                            ['P empty]
                            ['U (list (cons "R" (do mark! f 'R)))]
                            ;; xxx too squished for now
                            ['R (list (cons "S" (do mark! f 'S)))]
                            ['S (list (cons "U" (do mark! f 'U)))]))
                        (for/list ([l*u (in-list menu)])
                          `(a ([href ,(cdr l*u)]) ,(car l*u)))))))))))))))

  y-http)

(module+ main
  (require web-server/servlet-env)

  (match (current-command-line-arguments)
    [(vector)
     (serve/servlet (make-y-http)
                    #:launch-browser? #f
                    #:servlet-regexp #rx""
                    #:port 7331)]
    [(vector x)
     (parameterize ([current-directory ROOT])
       (system* (find-executable-path "youtube-dl")
                "--continue"
                "--ignore-errors"
                ;; "--embed-subs" "--all-subs"
                "--output"
                "U%(uploader)s - %(title)s.%(ext)s"
                x))]))
