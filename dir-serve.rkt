#lang racket/base
(require web-server/web-server
         (prefix-in files: web-server/dispatchers/dispatch-files)
         web-server/dispatchers/filesystem-map
         racket/cmdline)

(define the-port 8000)

(command-line
 #:once-each
 ["-p" port "the port to use" (set! the-port (string->number port))]
 #:args (base)
 (serve
  #:dispatch
  (files:make #:url->path (make-url->path base))
  #:port the-port))

(do-not-return)

