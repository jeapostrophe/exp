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
  (define-values (new-children id->node)
    (for/fold
     ([new-children empty]
      [id->node (hasheq)])
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
     (values (list* nc new-children)
             (hash-set id->node (node-id nc) nc))))
  (define new-games
    (struct-copy node games [children new-children]))

  (values id->node
          new-games))

;; Sort by ranking
(require racket/gui)
(define (id->info id)
  (node-label (hash-ref id->game id)))

(define (sort-by-ranking games-node ranking-db aspect)
  (define key (format "Sort~a" aspect))
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
  (define (add! fact)
    (match-define `(<= ,lhs ,rhs) fact)
    (set! ranking-db (list* fact ranking-db))
    (datalog! ranking-thy (! (<= lhs rhs))))

  (define (lift-<= x y)
    (not
     (empty?
      (datalog ranking-thy
               (? (<= x y))))))

  (define ask? #t)
  (define (unknown-<= x y)
    (cond
     [ask?
      (match
       (message-box/custom "Game Ranking"
                           (format "Better ~a" aspect)
                           (id->info x)
                           (id->info y)
                           "Stop Asking")
       [1
        (add! `(<= ,y ,x))]
       [2
        (add! `(<= ,x ,y))]
       [(or 3 #f)
        (set! ask? #f)])
      (inspect-<= x y)]
     [else
      #f]))

  (define mentioned? (make-hasheq))
  (define (inspect-<= x y)
    (cond
     [(lift-<= x y)
      (hash-set! mentioned? x #t)
      (hash-set! mentioned? y #t)
      #t]
     ;; By anti-symmetry
     [(lift-<= y x)
      (hash-set! mentioned? x #t)
      (hash-set! mentioned? y #t)
      #f]
     [else
      (unknown-<= x y)]))
  (define sorted-children
    (sort (shuffle games) (negate inspect-<=) #:key node-id))

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

  (values ranking-db
          (struct-copy node games-node [children new-children])))

(define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
(match-define (list games ranking meta) (with-input-from-file path read-org))

(define-values (id->game games*) (id-games games))
(match-define
 (list overall-ranking story-ranking mechanic-ranking)
 (with-input-from-string (apply string-append (node-content ranking))
   read))
(define-values (overall-ranking* games**)
  (sort-by-ranking games* overall-ranking "Overall"))
(define ranking*
  (struct-copy node ranking
               [content
                (list
                 (with-output-to-string
                   (λ ()
                      (write
                       (list overall-ranking* story-ranking mechanic-ranking)))))]))

(write-org (list games** ranking* meta))
