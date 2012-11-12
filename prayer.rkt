#lang racket/base
(require racket/list
         racket/match)

(define show-schedule
  (match-lambda
   [(list b l d t)
    (printf "Breakfast: ~a\n" b)
    (printf "    Lunch: ~a\n" l)
    (printf "   Dinner: ~a\n" d)
    (printf " Bed-time: ~a\n" t)]))

(define choices
  (list "Daddy" "Mommy" "The Frog" "Peach"))

(define schedules
  (for*/list ([b (in-list choices)]
              [l (in-list (remove* (list b "Daddy") choices))]
              [d (in-list (remove* (list b l) choices))]
              [t (in-list (remove* (list b l d) choices))])
    (list b l d t)))

(define how-many-schedules
  (length schedules))

(module+ main
  (show-schedule
   (list-ref schedules
             (modulo (date-year-day (seconds->date (current-seconds)))
                     how-many-schedules)))

  (serve/servlet 
   start
   #:listen-ip #f
   #:command-line? #t
   #:port 9005))
