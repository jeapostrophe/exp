#lang racket/base
(require net/giantbomb
         racket/list
         racket/match
         racket/format
         "org.rkt")

(module+ main
  (current-api-key
   "60fcf6401d6ad9c37f8daf603352fdedf36c6514")

  (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
  (match-define (list games meta) (with-input-from-file path read-org))

  (define (show-game ht)
    (printf "~a: ~a (~v)\n"
            ))

  (for/list ([g (in-list (node-children games))])
    (let/ec return
      (define ns (node-props g))
      (when (hash-has-key? ns "Release")
        (return g))

      (define n (node-label g))
      (printf "~v (~a ~a)\n"
              n
              (hash-ref ns "Year")
              (hash-ref ns "System"))

      (define gb-dates
        (for ([gb (in-list (game-search n))]
              [i (in-naturals)])
          (define gb-n (hash-ref gb 'name))
          (define gb-date (game-info-release gb))
          (define gb-platforms
            (map
             (λ (ht)
               (hash-ref ht 'name))
             (hash-ref
              (hash-ref
               (api-url->json
                (make-api-url
                 (list "game"
                       (number->string (hash-ref gb 'id))
                       "")
                 empty))
               'results)
              'platforms)))
          (printf "\t~a. ~a ~a: ~v\n"
                  i (~a #:min-width 10 gb-date) gb-n gb-platforms)
          gb-date))
      (printf "\ts. skip\n")
      (printf "\tq. quit\n")

      (match (read)))))
