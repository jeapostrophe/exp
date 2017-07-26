#lang racket/base
(require racket/list
         racket/port
         racket/match
         racket/file
         racket/system
         racket/function
         racket/gui
         racket/date
         file/org-mode)

(module+ main
  (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
  (match-define (list games meta) (with-input-from-file path read-org))
  (define k 0)
  (for ([g (in-list (node-children games))])
    (define p (node-props g))
    (when (equal? "Y" (hash-ref p "Owned" #f))
      (unless (hash-ref p "Price" #f)
        (set! k (add1 k))
        (printf "~a. ~a\n" k (node-label g))))))
