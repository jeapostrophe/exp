#lang racket/base
(require sxml/html)

(define (parse p)
  (define x (call-with-input-file p html->xexp))
  (format "~e" x))

(module+ main
  (parse (build-path (find-system-path 'home-dir)
                     "Downloads"
                     "COCA-5000.html")))
