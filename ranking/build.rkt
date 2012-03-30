#lang racket/base
(require racket/list
         racket/port
         racket/match
         racket/file
         racket/system
         racket/function
         racket/gui
         "org.rkt")

(struct bst (left val right) #:prefab)
(define sorted-list->binary-tree
  (match-lambda
   [(list)
    #f]
   [(list val)
    (bst #f val #f)]
   [l
    (define-values (before after)
      (split-at l (quotient (length l) 2)))
    (bst (sorted-list->binary-tree before)
         (first after)
         (sorted-list->binary-tree (rest after)))]))

(module+ test
  (require rackunit)
  (check-equal?
   (sorted-list->binary-tree '(0))
   (bst #f 0 #f))
  (check-equal?
   (sorted-list->binary-tree '(0 1))
   (bst (bst #f 0 #f) 1 #f))
  (check-equal?
   (sorted-list->binary-tree '(-1 0 1))
   (bst (bst #f -1 #f) 0 (bst #f 1 #f)))
  (check-equal?
   (sorted-list->binary-tree '(-3 -2 -1 0 1 2 3))
   #s(bst #s(bst #s(bst #f -3 #f) -2 #s(bst #f -1 #f)) 0 #s(bst #s(bst #f 1 #f) 2 #s(bst #f 3 #f)))))

(define binary-tree->sorted-list
  (match-lambda
   [#f
    empty]
   [(bst left v right)
    (append (binary-tree->sorted-list left)
            (list* v (binary-tree->sorted-list right)))]))

(module+ test
  (define (binary-tree-identity l)
    (check-equal? (binary-tree->sorted-list (sorted-list->binary-tree l))
                  l))

  (for ([i (in-range 10)])
    (binary-tree-identity (sort (build-list 10 (compose random add1)) <))))

(define (binary-insert x < a-bst)
  (match a-bst
    [#f
     (bst #f x #f)]
    [(bst left y right)
     (if (< x y)
       (bst (binary-insert x < left) y right)
       (bst left y (binary-insert x < right)))]))

(module+ test
  (check-equal?
   (binary-tree->sorted-list
    (binary-insert 5 <
                   (sorted-list->binary-tree '(-3 -2 -1 0 1 2 3))))
   '(-3 -2 -1 0 1 2 3 5)))

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

(define (perform-ranking kind games)
  (define key (format "Sort~a" kind))
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
                    key ((node-prop key #f) n))
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
                                (node-prop key +inf.0))))))
  (define-values
    (ranked unranked)
    (partition (node-prop key #f) finished-games))

  (define stop? #f)
  (define (game< a b)
    (match
        (message-box/custom
         "Ranking" (format "~a Which is better?" kind)
         (node-label a) (node-label b)
         "Stop Asking")
      [1 #t]
      [2 #f]
      [x
       (set! stop? #t)
       (game< a b)]))

  (define ranked*
    (node "Ranked" (hasheq) empty
          (let/ec esc
            (for/fold ([ranked ranked])
                ([unranked-game (in-list unranked)])
              (if stop?
                (esc ranked)
                (binary-tree->sorted-list
                 (binary-insert unranked-game game<
                                (sorted-list->binary-tree ranked))))))))
  (define ranked** (node-children (id-games ranked* key)))
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
          (hash-set (node-props n) key
                    ((node-prop key #f) ranked-n))])
        n)))

  (struct-copy
   node games
   [children games/SortOverall]))

;; XXX Gather more information from GiantBomb (like genre, etc)
(module+ main
  (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
  (match-define (list games meta) (with-input-from-file path read-org))
  (let*
      ((games
        (normalize-games games))

       (games
        (perform-ranking "Overall" games))

       (games
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

       (games
        (id-games
         (node-sort
          games
          (cmp->lt
           (2compose wordy-cmp node-label)))
         "SortAlpha")))
    (with-output-to-file path
      #:exists 'replace
      (λ () (write-org (list games meta))))))
