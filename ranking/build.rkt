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
(define (node-id n [def #f])
  (string->number
   (hash-ref (node-props n) "ID"
             (or def
                 (λ () (error 'node-id "Not present on ~e" n))))))
(define (id-games games)
  (define max-id
    (for/fold
        ([id -1])
        ([c (in-list (node-children games))])
      (max id (node-id c "-1"))))
  (define next-id
    (add1 max-id))
  (define new-children
    (for/list ([c (in-list (node-children games))])
      (define p (node-props c))
      (define cp
        (hash-set 
         (hash-remove* p
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
            "InProgress"]
           [("Y" "Y")
            "Done-PlayAgain"]
           [("Y" "M")
            "Done-MaybeAgain"])))
      (struct-copy
       node c
       [props
        (hash-set p "ID"
                  (or (hash-ref p "ID" #f)
                      (begin0 (number->string next-id)
                              (set! next-id (add1 next-id)))))])))
  (define new-games
    (struct-copy node games [children new-children]))

  new-games)

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

(define ((node-prop prop) node)
  (hash-ref (node-props node) prop #f))

(define status-cmp
  (match-lambda*
   [(#f #f) 'eq]))

(define (node-sort n <)
  (struct-copy node n [children (sort (node-children n) <)]))

(require racket/package)
(package-begin
 (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
 (match-define (list games meta) (with-input-from-file path read-org))

 ;; XXX Gather more information from GiantBomb (like genre, etc)
 (define* games (id-games games))
 (define* games (node-sort games
                      (cmp->lt
                       (cmp-then
                        (2compose status-cmp (node-prop "Status"))
                        (2compose number-cmp (node-prop "Year"))
                        (2compose string-cmp node-label)))))

 ;; XXX Compute the default sort that emacs does

 (write-org (list games meta)))
