#lang racket/base
(require racket/list
         racket/match
         "org.rkt")

(define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
(match-define (list games meta) (with-input-from-file path read-org))

(define max-id
  (for/fold
   ([id -1])
   ([c (in-list (node-children games))])
   (max id
        (string->number (hash-ref (node-props c) "ID" "-1")))))

(define next-id
  (add1 max-id))
(define new-games
  (struct-copy
   node games
   [children
    (for/list
     ([c (in-list (node-children games))])
     (define cp (node-props c))
     (struct-copy
      node c
      [props
       (hash-set cp "ID"
                 (or (hash-ref cp "ID" #f)
                     (begin0 (number->string next-id)
                             (set! next-id (add1 next-id)))))]))]))

(write-org (list new-games meta))

#;(write-org input)

;; XXX Go through and give everything an id
;; XXX Store a database of <= elements
;; XXX Request X of them when run
;; XXX Produce sorted list
