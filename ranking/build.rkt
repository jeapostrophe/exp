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
(define (sort-by-ranking id->game games-node ranking-db aspect)
  (define (id->info id)
    (define n (hash-ref id->game id))
    (define p (node-props n))
    (format "~a (~a, ~a)"
            (node-label n)
            (hash-ref p "Year" "")
            (hash-ref p "System" "")))
  (define key (format "Sort~a" aspect))
  (define all-games (node-children games-node))
  (define completed-games (filter game-completed? all-games))
  
  (define (add! fact)
    (match-define `(<= ,lhs ,rhs) fact)
    (set! ranking-db (list* fact ranking-db))
    (go-back!))

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
  (define (mentioned! x y)
    (unless (= x y)
            (hash-set! mentioned? x #t)
            (hash-set! mentioned? y #t)))

  (define (inspect-<= x y #:recur? [recur? #t])
    (cond
     ;; Reflexivity
     [(equal? x y)
      #t]
     ;; Knowledge
     [(member `(<= ,x ,y) ranking-db)
      (mentioned! x y)
      #t]     
     ;; XXX Transitivity
     [else
      (cond
       ;; Transitivity
       [(for/or 
         ([fact (in-list ranking-db)]
          #:when (equal? x (second fact)))
         (inspect-<= (third fact) y #:recur? #f))
        #t]
       ;; Anti-Symmetry
       [recur?
        (not (inspect-<= y x #:recur? #f))]
       ;; Ask
       [else
        (unknown-<= x y)])]))

  (define *done* #f)
  (define (compute-sort!)
    (sort (shuffle completed-games) inspect-<= #:key node-id))
  (define (go-back!)
    (*done* compute-sort!))

  (define sorted-completed-games
    ((let/cc done
             (set! *done* done)
             (go-back!))))

  (define id->order (make-hasheq))
  (for
   ([i (in-naturals)]
    [n (in-list sorted-completed-games)])
   (define id (node-id n))
   (when (hash-has-key? mentioned? id)
         (hash-set! id->order id i)))

  (define new-all-games
    (for/list
     ([n (in-list all-games)])
     (define sort-order (hash-ref id->order (node-id n) #f))
     (if sort-order
         (struct-copy
          node n
          [props
           (hash-set (node-props n) key sort-order)])
         n)))

  (values ranking-db
          (struct-copy node games-node [children new-all-games])))

(require racket/package)
(package-begin
 (define path "/home/jay/Dev/scm/github.jeapostrophe/home/etc/games.org")
 (match-define (list games ranking meta) (with-input-from-file path read-org))

 ;; XXX Gather more information from GiantBomb (like genre, etc)
 (define*-values (id->game games) (id-games games))
 (match-define
  (list overall-ranking story-ranking mechanic-ranking)
  (with-input-from-string (apply string-append (node-content ranking))
    read))
 (define*-values (overall-ranking games)
   (sort-by-ranking id->game games overall-ranking "Overall"))
 (define*-values (story-ranking games)
   (sort-by-ranking id->game games story-ranking "Story"))
 (define*-values (mechanic-ranking games)
   (sort-by-ranking id->game games mechanic-ranking "Mechanic"))
 ;; XXX Compute the default sort that emacs does
 (define* ranking
   (struct-copy node ranking
                [content
                 (list
                  (with-output-to-string
                    (λ ()
                       (write
                        (list overall-ranking story-ranking mechanic-ranking)))))]))

 (with-output-to-file path (λ () (write-org (list games ranking meta)))
                      #:exists 'replace)
 (message-box "Game Ranking" "Done!"))
