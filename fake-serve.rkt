#lang racket
(require web-server/web-server
         (prefix-in files: web-server/dispatchers/dispatch-files)
         racket/runtime-path)

(define-runtime-path the-file
  "/Users/jay/Downloads/The_Out-Cast_ep18.mp3")

(serve
 #:dispatch
 (files:make
  #:url->path
  (λ (url)
    (values
     the-file
     empty))
  #:path->mime-type
  (lambda (path)
    #"audio/mp3"))
 #:port 80)

(do-not-return)