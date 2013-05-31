#lang racket/base
(require racket/system
         racket/match
         racket/list
         racket/date
         racket/string
         racket/path)

(define (git-history-search p rx)
  (parameterize ([current-directory (path-only p)])
    (define-values (l-sp l-stdout l-stdin l-stderr)
      (subprocess #f #f #f
                  "/usr/bin/git"
                  "--no-pager"
                  "log"
                  "--format=format:%h %ct"
                  "--"
                  (file-name-from-path p)))

    (define seen? (make-hash))
    (for ([h (in-port read-line l-stdout)])
      (match-define (list sha ts) (string-split h))
      (define t (string->number ts))
      (define d (seconds->date t))
      (when (= 2 (date-week-day d))
        (define did (format "~a-~a" (date-year d) (date-year-day d)))
        (unless (hash-ref seen? did #f)
          (hash-set! seen? did #t)

          (define-values (s-sp s-stdout s-stdin s-stderr)
            (subprocess #f #f #f
                        "/usr/bin/git"
                        "--no-pager"
                        "show"
                        (format "~a:./~a" 
                                sha (file-name-from-path p))))
          
          (define lines
            (for/list ([sl (in-port read-line s-stdout)]
                       #:when (regexp-match rx sl))
              sl))

          (unless (empty? lines)
            (printf "Week of ~a\n" (date->string d))
            (for-each displayln lines))

          (subprocess-wait s-sp))))

    (subprocess-wait l-sp)))

(module+ main
  (git-history-search "/home/jay/Dev/scm/github.jeapostrophe/home/etc/work.org"
                      #rx"^\\*\\*\\* .+ - .*(?i:ECS|Scratch|CSTA|Alicia|Brenda|Board|Helen)"))
