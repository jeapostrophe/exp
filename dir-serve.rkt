#lang racket/base
(require web-server/web-server
         (prefix-in files: web-server/dispatchers/dispatch-files)
         web-server/dispatchers/filesystem-map
         racket/cmdline)

(command-line
 #:args (base)
 (serve
  #:dispatch
  (files:make #:url->path (make-url->path base))
  #:port 8000))

(do-not-return)

