#lang at-exp racket/base
(require racket/match
         racket/sequence
         racket/list
         racket/set
         csv-reading
         non-det
         raart)

(define (go! test p)
  (define in
    (call-with-input-file p
      (λ (ip)
        (csv->list
         (make-csv-reader ip)))))
  (match-define (cons (cons _ slots) candidates) in)
  (define i->slot
    (for/hasheq ([s (in-list slots)]
                 [i (in-naturals)])
      (values i s)))
  (define how-many-slots (hash-count i->slot))
  (define all-opts (sequence->list (in-range how-many-slots)))
  (define candidate-infos
    (for/list ([c (in-list candidates)]
               [i (in-naturals)])
      (match-define (cons name openings) c)
      (define file-opts
        (for/list ([o (in-list openings)]
                   [j (in-naturals)]
                   #:when (test o))
          j))
      (define opts
        (cond
          [(empty? file-opts)
           (eprintf "WARNING: ~a has no response, dropped from schedule.\n" name)
           #f]
          [else
           ;; We prefer later in the day/week
           (reverse file-opts)]))
      (cons name opts)))
  (define sorted-candidate-infos
    (sort (filter cdr candidate-infos) <=
          #:key (λ (ci) (length (cdr ci)))
          #:cache-keys? #t))

  (define (search available slot->candidate cis)
    (match cis
      ['() (ans slot->candidate)]
      [(cons (cons name opts) more)
       (ndo [the-opt (ans* (in-list opts))]
            (if (set-member? available the-opt)
              (search (set-remove available the-opt)
                      (hash-set slot->candidate the-opt name)
                      more)
              fail))]))

  (define sols
    (nrun #:k 1 #:mode 'dfs
          (search (list->seteq all-opts) (hasheq)
                  sorted-candidate-infos)))

  (define the-sol
    (if (empty? sols)
      (error 'fac-search "Unsatisfiable")
      (first sols)))
  (draw-here
   (table
    #:frames? #t
    #:inset-dw 2
    #:halign '(right left)
    (text-rows
     (for/list ([i (in-range how-many-slots)])
       (list
        (text (hash-ref i->slot i))
        (text (hash-ref the-sol i ""))))))))

(module+ main
  (go!
   ;; x is the person's choice and my preference
   ;; y is the person's choice
   (λ (o) (string=? o "x"))
   #;(λ (o) (not (string=? o "")))
   (build-path (find-system-path 'home-dir)
               "Downloads"
               "Candidate Rating Matrix - Phone Planning.csv")))
