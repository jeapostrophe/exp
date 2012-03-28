#lang scheme
(require xml
         (prefix-in 19: srfi/19)
         scheme/runtime-path
         web-server/http/xexpr
         web-server/servlet
         web-server/servlet-env)

(define-runtime-path the-dir "Retronauts")
(define the-files
  (reverse
   (filter (lambda (p)
             (regexp-match #".mp3$" (path->string p)))
           (directory-list the-dir))))

(define (pad i)
  (cond 
    [(< i 10)
     (format "000~a" i)]
    [(< i 100)
     (format "00~a" i)]
    [(< i 1000)
     (format "0~a" i)]
    [else
     (number->string i)]))

(define (start req)
  (response/xexpr
   `(rss ([version "2.0"])
                (channel
                 (title "Retronauts (Old)")
                 (description "Old episodes of Retronauts")
                 (language "en-us")
                 (copyright "")
                 (lastBuildDate "Fri, 14 Aug 2009 06:03:49 GMT")
                 (webMaster "jay.mccarthy@gmail.com")
                 (ttl "1")
                 ,@(for/list ([p (in-list the-files)]
                              [i (in-naturals)])
                     (define-values (month-s day-s year-s)
                       (match (path->string p)
                         [(regexp #rx"^(..)(..)(..)\\.mp3$" (list _ month-s day-s year-s))
                          (values month-s day-s year-s)]
                         [(regexp #rx"^(..)(..)(..)_02\\.mp3$" (list _ month-s day-s year-s))
                          (values month-s day-s year-s)]
                         [(regexp #rx"^R(..)(..)(..)\\.mp3$" (list _ month-s day-s year-s))
                          (values month-s day-s year-s)]))
                     (define d
                       (19:string->date (format "~a-~a-~a 12:00:00"
                                                day-s month-s                                                 
                                                (+ 2000 (string->number year-s)))
                                        "~d-~m-~Y ~H:~M:~S"))
                     `(item (title ,(path->string p))
                            (pubDate 
                             ,(19:date->string d "~a, ~d ~b ~Y ~T ~z"))
                            (description ,(path->string p))
                            (enclosure ([url ,(format "http://localhost:8080/~a" (path->string p))]
                                        [type "audio/mpeg"]))))))
   
   #:mime-type #"application/rss+xml"
   #:preamble #"<?xml version=\"1.0\"?>"))

(serve/servlet start
               #:port 8080
               #:servlet-path "/index.rss"
               #:launch-browser? #f
               #:extra-files-paths
               (list the-dir))