#lang racket/base
(require racket/list
         racket/port
         racket/match
         "org.rkt")

;; Helpers
(define (game-completed? n)
  (regexp-match #rx"^Y"
                (hash-ref (node-props n) "Completed" "N")))

;; Go through and give everything an id
(define (node-id n)
  (string->number (hash-ref (node-props n) "ID")))
(define (id-games games)
  (define max-id
    (for/fold
     ([id -1])
     ([c (in-list (node-children games))])
     (max id
          (string->number (hash-ref (node-props c) "ID" "-1")))))

  (define next-id
    (add1 max-id))
  (define id->node (make-hasheq))
  (define new-games
    (struct-copy
     node games
     [children
      (for/list
       ([c (in-list (node-children games))])
       (define cp (node-props c))
       (define nc
         (struct-copy
          node c
          [props
           (hash-set cp "ID"
                     (or (hash-ref cp "ID" #f)
                         (begin0 (number->string next-id)
                                 (set! next-id (add1 next-id)))))]))
       (hash-set! id->node (node-id nc) nc)
       nc)]))

  (values id->node
          new-games))

;; Sort by ranking
(define (sort-by-ranking games-node ranking-db key)
  (define all-games (node-children games-node))
  (define games (filter game-completed? all-games))
  (local-require datalog)
  (define ranking-thy (make-theory))
  (datalog!
   ranking-thy
   ;; Transitivity
   (! (:- (<= A C)
          (<= A B)
          (<= B C)))
   ;; Reflexivity
   (! (:- (<= A B)
          (= A B))))
  ;; Knowledge
  (for ([order (in-list ranking-db)])
       (match-define `(<= ,lhs ,rhs) order)
       (datalog! ranking-thy (! (<= lhs rhs))))

  (define (lift-<= x y)
    (not
     (empty?
      (datalog ranking-thy
               (? (<= x y))))))

  (define *unknowns* empty)
  (define (inspect-<= x y)
    (cond
     [(lift-<= x y)
      #t]
     ;; By anti-symmetry
     [(lift-<= y x)
      #f]
     [else
      (set! *unknowns*
            (list* (cons x y)
                   *unknowns*))
      #f]))
  (define sorted-children
    (sort (shuffle games) inspect-<= #:key node-id))

  (define new-children
    (for/list
     ([i (in-naturals)]
      [n (in-list sorted-children)])
     (struct-copy
      node n
      [props
       (hash-set (node-props n)
                 key
                 i)])))

  (values *unknowns*
          (struct-copy node games-node [children new-children])))

(define how-many-to-query 5)
(define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
(match-define (list games ranking meta) (with-input-from-file path read-org))

(define-values (id->game games*) (id-games games))
(match-define
 (list overall-ranking story-ranking mechanic-ranking)
 (with-input-from-string (apply string-append (node-content ranking))
   read))
(define-values (unknown-overall games**)
  (sort-by-ranking games* overall-ranking "OverallRanking"))

(require racket/gui)
#;(for ([i (in-range how-many-to-query)]
[x*y (in-list unknown-overall)])
(match-define (cons x y) x*y)
(define (id->info id)
  (node-label (hash-ref id->game id)))

(message-box/custom "Game Ranking"
                    "Which game is better, overall?"
                    (id->info x)
                    (id->info y)
                    #f))

(write-org (list games** ranking meta))

;; XXX Store a database of <= elements
;; XXX Request X of them when run
;; XXX Produce sorted list
