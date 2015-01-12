#!/usr/bin/env racket
#lang racket/base

(define (retouch! ps)
  (for/fold ([new-mtime #f])
            ([p (in-list ps)])
    (define old-mtime (file-or-directory-modify-seconds p))
    (cond
     [(and new-mtime (< old-mtime new-mtime))
      (printf "retouch ~v ~a\n" p new-mtime)
      (file-or-directory-modify-seconds p new-mtime)
      (+ 1 new-mtime)]
     [else
      (+ 1 old-mtime)])))

(module+ main
  (require racket/cmdline)
  (command-line #:program "retouch"
                #:args files
                (retouch! files)))
