#lang racket/base
(require racket/pretty
         racket/list
         racket/match
         csv-reading
         raart)

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
        ;; "160-L-C" 1 ;; 2 on site, but 315 allocated to Holly
        ;; "170-R-C" 2
        ))
(define MAX-POSSIBLE (hash-count inventory))

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

(define assistant '("Anna Rumshisky" "Wenjin Zhou" "Matteo Cimini" "Michelle Ichinco" "Farhad Pourkamali Anaraki" "Ben Kim" "Reza Ahmadzadeh"))
(define associate '(#;"Bill Moloney" #;"Byung Kim" "Cindy Chen" "Tingjian Ge" "Guanling Chen" "Yu Cao" "Jay McCarthy"))
(define full '(#;"Jie Wang" "Benyuan Liu" #;"Xinwen Fu" "Hong Yu"))
(define lecturer '("David Adams" "Sirong Lin" "Yelena Rykalova" "C. Tom Wilkes" "Jonathan Mwaura"))

(define (go! who->prefs)
  ;; Problem Instance
  (struct state (name score seen assignment))

  (define best #f)
  (define best-sc -inf.0)
  (define past '())
  (define (try! #:keep? [keep? #f] name order)
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
            (and (< 0 (hash-ref inv (cdr p) 0))
                 p)))
        (values (hash-update inv room-type sub1)
                (+ score this-score)
                (hash-set assignment who (list room-type this-score)))))
    (define st-sc (state-score st))
    (cond
      [(< best-sc st-sc)
       (when best (set! past (cons best past)))
       (set! best st)
       (set! best-sc st-sc)
       (eprintf "New best! ~a ~v\n" name st-sc)]
      [keep?
       (set! past (cons st past))]))

  ;; Run problem
  (try! #:keep? #t "FAAL" (append full associate assistant lecturer))
  (define-syntax-rule (qlist e ...) (list (cons 'e e) ...))
  (for ([o (in-permutations (qlist assistant lecturer full associate))])
    (try! (map car o) (append-map cdr o)))
  (define all (append full associate assistant lecturer))
  (define random-k 0)
  (define random-t
    (thread
     (λ ()
       (for ([i (in-naturals)])
         (try! (cons 'random i) (shuffle all))
         (set! random-k (add1 random-k))))))

  ;; Render Solution
  (define max-score (* MAX-POSSIBLE (length all)))
  (draw-here
   (vappend
    #:halign 'center
    (table #:inset-dw 1
           (text-rows
            (list* (list "Strategy" "Score" "%")
                   (for/list ([s (in-list (reverse (cons best past)))])
                     (match-define (state name score seen assignment) s)
                     (list name score (real->decimal-string (/ score max-score)))))))
    (table #:inset-dw 1
           (text-rows
            (list* (list "Who" "Room" "Score")
                   (for/list ([(k v) (in-hash (state-assignment best))])
                     (cons k v))))))))

(module+ main
  (go! (parse (build-path (find-system-path 'home-dir) "Downloads"
                          "Pasteur Offices - Form Responses 1.csv"))))
