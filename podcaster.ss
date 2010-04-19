#lang scheme
(require xml
         scheme/runtime-path
         web-server/servlet
         web-server/servlet-env)

(define-runtime-path the-dir "Retroforce GO!")
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
  (list #"application/rss+xml"
        #"<?xml version=\"1.0\"?>"
        (string->bytes/utf-8
         (xexpr->string
          `(rss ([version "2.0"])
                (channel
                 (title "Retroforce GO! (Old)")
                 (description "Old episodes of Retroforce Go!")
                 (language "en-us")
                 (copyright "")
                 (lastBuildDate "Fri, 14 Aug 2009 06:03:49 GMT")
                 (webMaster "jay.mccarthy@gmail.com")
                 (ttl "1")
                 ,@(for/list ([p (in-list the-files)]
                              [i (in-naturals)])
                     `(item (title ,(path->string p))
                            (pubDate ,(format "Wed, 15 Jun ~a 19:00:00 GMT"
                                              (pad (- 2000 i))))
                            (description ,(path->string p))
                            (enclosure ([url ,(format "http://localhost:8080/~a" (path->string p))]
                                        [type "audio/mpeg"]))))))))))

(serve/servlet start
               #:port 8080
               #:servlet-path "/index.rss"
               #:launch-browser? #f
               #:extra-files-paths
               (list the-dir))