#lang racket/base
(require racket/list
         racket/match
         2htdp/batch-io)

;; Data is available at http://darksoulswiki.wikispaces.com/Armor
(define positions '("Torso" "Legs" "Arms" "Head"))

(define option-row->option
  (match-lambda
   [(list name durability weight phys str sls prc mag fir lit poise bleed poison curse)
    (define vals (map string->number (list weight phys)))
    (and (andmap number? vals)
         (list* name vals))]))

(define options
  (for/list ([p (in-list positions)])
    (define pth (format "/home/jay/Downloads/Dark Souls Armor - ~a.csv" p))
    (sort
     (remove-duplicates (cons (list (format "Bare ~a" p) 0.0 0.0)
                                 (filter-map option-row->option (rest (read-csv-file pth))))
                           #:key rest)
     <=
     #:key third)))

(printf "option structure: ~v\n" (map length options))
(printf "~v options\n" (apply * (map length options)))

(define (branch-and-bound target-weight current-value options)
  (match options
    [(list)
     current-value]
    [(list* option options)
     (for/fold ([best-so-far -inf.0])
         ([choice (in-list option)])
       (match-define (list* _ weight phys _) choice)
       (define new-weight (- target-weight weight))
       (cond
         [(negative? new-weight)
          best-so-far]
         [else
          (define new-value (+ current-value phys))
          (define this-value (branch-and-bound new-weight new-value options))
          (cond
            [(> this-value best-so-far)
             this-value]
            [else
             best-so-far])]))]))

(branch-and-bound (/ 78 2) 0 options)
