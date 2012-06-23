#lang racket/base
(require racket/list
         racket/match
         2htdp/batch-io)

;; Data is available at http://darksoulswiki.wikispaces.com/Armor
(define positions '("Torso" "Legs" "Arms" "Head"))

(define option-row->option
  (match-lambda
   [(list name durability weight phys str sls prc mag fir lit poise bleed poison curse have)
    (define vals (map string->number (list weight phys poise)))
    (and (andmap number? vals)
         #;(string=? "1" have)
         #;(not (regexp-match (regexp-quote "+") name))
         (list* name vals))]))

(define options
  (for/list ([p (in-list positions)])
    (define pth (format "/home/jay/Downloads/Dark Souls Armor - ~a.csv" p))

    (define choices
      (cons (list (format "Bare ~a" p) 0 0 0)
            (filter-map option-row->option (read-csv-file pth))))

    (for/fold ([ht (hash)])
        ([c (in-list choices)])
      (match-define (list* name weight phys _) c)
      (hash-update ht weight
                   (λ (old)
                     (match-define (list* _ _ old-phys _) old)
                     (if (> old-phys phys)
                       old
                       c))
                   c))))

(printf "option structure: ~v\n" (map hash-count options))
(printf "~v options\n" (apply * (map hash-count options)))

(define (branch-and-bound target-weight current-value options)
  (match options
    [(list)
     (values current-value empty)]
    [(list* option options)
     (for/fold ([best-so-far -inf.0]
                [best-so-far-choice #f])
         ([(weight choice) (in-hash option)]
          #:when (<= weight target-weight))
       (match-define (list* _ weight phys _) choice)
       (define new-weight (- target-weight weight))
       (define new-value (+ current-value phys))
       (define-values (this-value sub-choice) (branch-and-bound new-weight new-value options))
       (cond
         [(> this-value best-so-far)
          (values this-value (list* choice sub-choice))]
         [else
          (values best-so-far best-so-far-choice)]))]))

(define-values (_ choices) 
  #;(branch-and-bound (- (/ 80 2)
                       #;6 5
                       3 #;3.5) 0 options)
    (branch-and-bound (- (/ 120 2)
                       6 6) 0 options))

(printf "\nBest choices:\n")
(printf "Total ~a\n"
        (for/fold ([tots (list 0 0 0)])
            ([c (in-list choices)])
          (match-define (list* name vals) c)
          (printf " ~a ~a\n" vals name)
          (map + tots vals)))
