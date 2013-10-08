#lang racket/base
(require web-server/web-server
         web-server/http
         (prefix-in files: web-server/dispatchers/dispatch-files)
         (prefix-in seq: web-server/dispatchers/dispatch-sequencer)
         (prefix-in lift: web-server/dispatchers/dispatch-lift)
         web-server/dispatchers/filesystem-map
         racket/cmdline)

(define the-port 8000)

(command-line
 #:once-each
 ["-p" port "the port to use" (set! the-port (string->number port))]
 #:args (base)
 (serve
  #:dispatch
  (seq:make (files:make #:url->path (make-url->path base))
            (lift:make (λ (req) (response/xexpr "Fail"))))
  #:port the-port))

(do-not-return)

