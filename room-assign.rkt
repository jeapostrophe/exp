#lang racket/base
(require racket/pretty
         racket/list
         racket/match
         non-det/opt
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

(define assistant '("Anna Rumshisky" "Wenjin Zhou" "Matteo Cimini" "Michelle Ichinco" "Farhad Pourkamali Anaraki" "Ben Kim" "Reza Ahmadzadeh"))
(define associate '("William Moloney" "Byung Kim" "Cindy Chen" "Tingjian Ge" "Guanling Chen" "Yu Cao" "Jay McCarthy"))
(define full '("Jie Wang" "Benyuan Liu" "Xinwen Fu" "Hong Yu"))
(define lecturer '("David Adams" "Sirong Lin" "Yelena Rykalova" "C. Tom Wilkes" "Jonathan Mwaura"))

(define (go! who->prefs)
  ;; Problem Instance
  (struct state (unseen inv score-bound score seen assignment))

  (define K 0)
  (define (branch st)
    (set! K (add1 K)) (printf "K=~a\n" K)
    (match-define (state unseen inv score-bound score seen assignment) st)
    (match-define (cons who next-unseen) unseen)
    (for/list ([p (in-list (take (filter (λ (p) (< 0 (hash-ref inv (cdr p))))
                                         (hash-ref who->prefs who))
                                 ;; XXX Consider on the top 3 options
                                 3))])
      (match-define (cons this-score room-type) p)
      (define next-inv (hash-update inv room-type sub1))
      (define next-bound
        (+ score (for/sum ([u (in-list unseen)])
                   (for/or ([p (in-list (hash-ref who->prefs u))]
                            #:when (< 0 (hash-ref inv (cdr p))))
                     (car p)))))
      (candidate*
       (state next-unseen next-inv next-bound (+ score this-score)
              (cons who seen) (hash-set assignment who room-type)))))
  (define (candidate* st)
    (if (empty? (state-unseen st))
      (solution state-score st)
      (candidate state-score-bound branch st)))

  ;; Problem Setup
  (define heuristics
    (for/list ([heur
                (list (vector "ALFA" (append assistant lecturer full associate))
                      (vector "FAAL" (append full associate assistant lecturer)))])
      (match-define (vector name order) heur)
      (candidate*
       (for/fold ([inv inventory]
                  [score 0] [assignment (hash)]
                  #:result
                  (state '() inv score score order assignment))
                 ([who (in-list order)]
                  #:when (hash-has-key? who->prefs who))
         (define prefs (hash-ref who->prefs who))
         (match-define (cons this-score room-type)
           (for/or ([p (in-list prefs)])
             (and (< 0 (hash-ref inv (cdr p)))
                  p)))
         (values (hash-update inv room-type sub1)
                 (+ score this-score)
                 (hash-set assignment who room-type))))))
  (define initial-st
    (state
     ;; Start with people who prefer rooms with many in the inventory
     (sort (hash-keys who->prefs) >
           #:cache-keys? #t
           #:key (λ (w)
                   (hash-ref inventory (cdr (first (hash-ref who->prefs w))))))
     inventory (* 11 (hash-count who->prefs)) 0 '() (hash)))
  (define sol
    (optimize #:mode 'max (candidate* initial-st)
              heuristics))

  ;; Render Solution
  (let ()
    (define max-score (* 11 (hash-count who->prefs)))
    (match-define (state unseen inv score-bound score seen assignment) sol)
    (printf "Order: ~a\n" seen)
    (pretty-print assignment)
    (printf "Score is ~a (~a)\n" score
            (real->decimal-string (/ score max-score)))))

(module+ main
  (go! (parse (build-path (find-system-path 'home-dir) "Downloads"
                          "Pasteur Offices - Form Responses 1.csv"))))
