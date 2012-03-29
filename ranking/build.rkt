#lang racket/base
(require racket/list
         racket/port
         racket/match
         "org.rkt")

;; Helpers
(define (game-completed? n)
  (regexp-match #rx"^Y"
                (hash-ref (node-props n) "Completed" "N")))

(define (hash-remove* ht . ks)
  (for/fold ([ht ht]) ([k (in-list ks)])
    (hash-remove ht k)))

;; Go through and give everything an id
(define (number->string/padding n max)
  (define ms-len (string-length (number->string max)))
  (define s (number->string n))
  (define s-len (string-length s))
  (string-append (make-string (- ms-len s-len) #\0)
                 s))
(define (id-games games id)
  (define how-many (length (node-children games)))
  (define new-children
    (for/list ([c (in-list (node-children games))]
               [this-id (in-naturals)])
      (define cp (node-props c))
      (struct-copy
       node c
       [props
        (hash-set cp id (number->string/padding this-id how-many))])))
  (struct-copy node games [children new-children]))

(define (normalize-games games)
  (define new-children
    (for/list ([c (in-list (node-children games))])
      (define p (node-props c))
      (define cp
        (if (hash-has-key? p "Status")
          p
          (hash-set
           (hash-remove* p
                         "ID"
                         "Completed"
                         "PlayAgain"
                         "Reviewed"
                         "SortOverall"
                         "SortStory"
                         "SortMechanic")
           "Status"
           (match* ((hash-ref p "Completed" #f) (hash-ref p "PlayAgain" #f))
             [("Scheduled" _)
              "Scheduled"]
             [("Completed" #f)
              "Done"]
             [("Queue" _)
              "Queue"]
             [("N" "M")
              #f]
             [((or "Y" "Y*" "N") "N")
              "Done-NeverAgain"]
             [(#f #f)
              #f]
             [("Started" #f)
              #f]
             [("Y" "Y")
              "Done-PlayAgain"]
             [("Y" "M")
              "Done-MaybeAgain"]))))
      (struct-copy
       node c
       [props cp])))
  (struct-copy node games [children new-children]))

;; Sort by ranking
(define (cmp->lt cmp)
  (λ (a b)
    (eq? 'lt (cmp a b))))
(define (cmp-null a b)
  'eq)
(define (cmp-then2 fst snd)
  (λ (a b)
    (match (fst a b)
      ['eq (snd a b)]
      [x x])))
(define (cmp-then . cmps)
  (foldr cmp-then2 cmp-null cmps))
(define (2compose snd fst)
  (λ (a b)
    (snd (fst a) (fst b))))

(define (number-cmp a b)
  (cond
    [(= a b) 'eq]
    [(< a b) 'lt]
    [else 'gt]))
(define (string-cmp a b)
  (cond
    [(string=? a b) 'eq]
    [(string-ci<? a b) 'lt]
    [else 'gt]))

(define (string->words s)
  (regexp-split #rx" " s))

(define (point-list-cmp cmp)
  (define loop
    (match-lambda*
     [(list (list* a as)
            (list* b bs))
      (match (cmp a b)
        ['eq (loop as bs)]
        [x x])]
     [(list (list) (list))
      'eq]
     [(list (list* a as) (list))
      'gt]
     [_
      'lt]))
  loop)

(define (word-cmp as bs)
  (define an (string->number as))
  (define bn (string->number bs))
  (if (and (number? an) (number? bn))
    (number-cmp an bn)
    (string-cmp as bs)))

(define wordy-cmp
  (2compose (point-list-cmp word-cmp) string->words))

(define (string->number/exn s)
  (or (string->number s)
      (error 'string->number/exn "Not a number string: ~e" s)))

(define ((node-prop prop) node)
  (hash-ref (node-props node) prop))

(define (list-index e l)
  (cond
    [(empty? l)
     (error 'list-index "Not in list: ~e" e)]
    [(equal? e (first l))
     0]
    [else
     (add1 (list-index e (rest l)))]))

(define (list->cmp ordering)
  (λ (a b)
    (number-cmp (list-index a ordering)
                (list-index b ordering))))
(define status-cmp
  (list->cmp
   (list "Active" "Scheduled" "Queue"
         #f
         "Done-PlayAgain" "Done" "Done-MaybeAgain" "Done-NeverAgain")))

(define (node-sort n <)
  (struct-copy node n [children (sort (node-children n) <)]))

(require racket/package)
(package-begin
 (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
 (match-define (list games meta) (with-input-from-file path read-org))

 ;; XXX Gather more information from GiantBomb (like genre, etc)
 (define* games
   (normalize-games games))
 ;; XXX Export the list of games to an org to have me re-arrange it
 ;; and then bring it back in and label them.
 (define* games
   (id-games
    (node-sort
     games
     (cmp->lt
      (cmp-then
       (2compose status-cmp (node-prop "Status"))
       ;; XXX sort by when I last played the game
       (2compose number-cmp (compose string->number/exn (node-prop "Year")))
       (2compose wordy-cmp node-label))))
    "SortNormal"))
 (define* games
   (id-games
    (node-sort
     games
     (cmp->lt
      (2compose wordy-cmp node-label)))
    "SortAlpha"))

 (write-org (list games meta)))
