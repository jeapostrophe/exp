#lang racket/base
(require racket/pretty
         racket/list
         racket/match
         csv-reading)

(define (parse p)
  (match-define (list* head fac)
    (csv->list (make-csv-reader (open-input-file p))))
  (define opts
    (map (λ (x) (second (regexp-match #rx"\\[(.*?)\\]$" x)))
         (list-tail head 2)))
  (for/hash ([f (in-list fac)])
    (match-define (list* _ name prefs) f)
    (values name
            (sort
             (for/list ([p (in-list prefs)] [o (in-list opts)])
               (cons (string->number p) o))
             >= #:key car))))

(define inventory
  (hash "110-C-C" 1
        "120-L-T" 2
        "120-L-C" 4
        "120-C-C" 1
        "120-R-T" 5
        "140-C-C" 3
        "140-C-T" 1
        "140-R-C" 4
        "150-C-T" 6
        "160-L-C" 1 ;; 2 on site, but 315 allocated to Holly
        "170-R-C" 2))

(define (go! who->prefs)
  (define order (hash-keys who->prefs))

  (for/fold ([inv inventory]
             [score 0] [max-score 0] [assignment '()]
             #:result
             (let ()
               (pretty-print assignment)
               (printf "Score is ~a (~a)\n" score
                       (real->decimal-string (/ score max-score)))))
            ([who (in-list order)]
             #:when (hash-has-key? who->prefs who))
    (define prefs (hash-ref who->prefs who))
    (match-define (cons this-score room-type)
      (for/or ([p (in-list prefs)])
        (and (< 0 (hash-ref inv (cdr p)))
             p)))
    (values (hash-update inv room-type sub1)
            (+ score this-score)
            (+ max-score 11)
            (list* (cons who room-type) assignment))))

(module+ main
  (go! (parse (build-path (find-system-path 'home-dir) "Downloads"
                          "Pasteur Offices - Form Responses 1.csv"))))
