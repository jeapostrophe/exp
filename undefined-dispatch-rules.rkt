#lang racket/base
(require web-server/dispatch)

(define (make-site param)
  (define-values (main-dispatch main-url)
    (dispatch-rules
     [("a") a]
     [("b") b]))

  (define (good-footer)
    (list (main-url a)
          (main-url b)))

  (define bad-footer
    (list (main-url a)
          (main-url b)))

  (define (a req)
    (list "A" param (good-footer) bad-footer))

  (define (b req)
    (list "B" param (good-footer) bad-footer))

  main-dispatch)

(require rackunit
         net/url
         web-server/http
         racket/promise
         racket/list)
(check-equal?
 ((make-site "customization")
  (make-request #"GET" (string->url "/a") empty (delay #"")
                #"" "127.0.0.1" 80 "127.0.0.1"))
 (list "A" 
       "customization"
       (list "/a" "/b")
       (list "/a" "/a")))
