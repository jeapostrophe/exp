#lang racket/base
(require racket/pretty
         racket/list
         racket/match
         csv-reading
         raart)

(define MAX-POSSIBLE 11)

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
               (cons (min MAX-POSSIBLE (string->number p)) o))
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
  (struct state (name score seen assignment))

  (define best #f)
  (define best-sc -inf.0)
  (define past '())
  (define K 0)
  (define (try! #:keep? [keep? #f] name order)
    (set! K (add1 K)) (printf "~a\n" K)
    (define st
      (for/fold ([inv inventory]
                 [score 0] [assignment (hash)]
                 #:result
                 (state name score order assignment))
                ([who (in-list order)]
                 #:when (hash-has-key? who->prefs who))
        (define prefs (hash-ref who->prefs who))
        (match-define (cons this-score room-type)
          (for/or ([p (in-list prefs)])
            (and (< 0 (hash-ref inv (cdr p)))
                 p)))
        (values (hash-update inv room-type sub1)
                (+ score this-score)
                (hash-set assignment who room-type))))
    (define st-sc (state-score st))
    (cond
      [(< best-sc st-sc)
       (when best (set! past (cons best past)))
       (set! best st)
       (set! best-sc st-sc)]
      [keep?
       (set! past (cons st past))]))

  ;; Run problem
  (try! #:keep? #t "FAAL" (append full associate assistant lecturer))
  (define-syntax-rule (qlist e ...) (list (cons 'e e) ...))
  (for ([o (in-permutations (qlist assistant lecturer full associate))]
        [i (in-naturals)])
    (try! (map car o) (append-map cdr o)))
  (define all (hash-keys who->prefs))
  (for ([i (in-range (expt 2 20))])
    (try! (cons 'random i) (shuffle all)))

  ;; Render Solution
  (define max-score (* MAX-POSSIBLE (hash-count who->prefs)))
  (draw-here
   (table #:inset-dw 1
          (text-rows
           (list* (list "Name" "Score" "%")
                  (for/list ([s (in-list (reverse (cons best past)))])
                    (match-define (state name score seen assignment) s)
                    (list name score (real->decimal-string (/ score max-score)))))))))

(module+ main
  (go! (parse (build-path (find-system-path 'home-dir) "Downloads"
                          "Pasteur Offices - Form Responses 1.csv"))))
