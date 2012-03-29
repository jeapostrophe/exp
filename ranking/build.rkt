#lang racket/base
(require racket/list
         racket/port
         racket/match
         racket/file
         racket/system
         racket/function
         "org.rkt")

;; Helpers
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

(define ((node-prop prop . more) node)
  (apply hash-ref (node-props node) prop more))

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

 (define*
   games
   (let ()
     (define (game-completed? n)
       (regexp-match #rx"^Done"
                     (or (hash-ref (node-props n) "Status" #f)
                         "Queue")))
     (define (sortable l)
       (for/list ([n (in-list l)])
         (node (format "~a (~a, ~a)"
                       (node-label n)
                       ((node-prop "System") n)
                       ((node-prop "Year") n))
               (hasheq "ID" ((node-prop "ID") n)
                       "SortOverall" ((node-prop "SortOverall" #f) n))
               empty
               empty)))

     (define the-games
       (node-children (id-games games "ID")))
     (define finished-games
       (sortable
        (sort (filter game-completed? the-games)
              (2compose < (compose (λ (n)
                                     (if (number? n)
                                       n
                                       (string->number n)))
                                   (node-prop "SortOverall" +inf.0))))))
     (define-values
       (ranked unranked)
       (partition (node-prop "SortOverall" #f) finished-games))

     ;; XXX change this so that we do a binary insertion of each thing
     ;; in unranked.
     (define t (make-temporary-file "tmp~a.org"))
     (with-output-to-file t
       #:exists 'replace
       (λ ()
         (write-org (list (node "Ranked" (hasheq) empty
                                ranked)
                          (node "Unranked" (hasheq) empty
                                unranked)))))
     (system* "/usr/bin/emacsclient" "-c" t)
     (match-define (list ranked* unranked*) (with-input-from-file t read-org))
     (delete-file t)
     (define ranked** (node-children (id-games ranked* "SortOverall")))
     (define games/SortOverall
       (for/list ([n (in-list (node-children games))]
                  [i (in-naturals)])
         (define ranked-n
           (findf (compose (curry = i) string->number (node-prop "ID"))
                  ranked**))
         (if ranked-n
           (struct-copy
            node n
            [props
             (hash-set (node-props n) "SortOverall"
                       ((node-prop "SortOverall" #f) ranked-n))])
           n)))

     (struct-copy
      node games
      [children games/SortOverall])))

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

 (with-output-to-file path
   #:exists 'replace
   (λ () (write-org (list games meta)))))
