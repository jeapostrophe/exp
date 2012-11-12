#lang racket/base
(require racket/list
         racket/match
         racket/function)

(define (tdize v)
  `(td ,v))

(define choices
  (list "Daddy" "Mommy" "Frog" "Peach"))

(define schedules
  (shuffle
   (for*/list ([b (in-list choices)]
               [l (in-list (remove* (list b "Daddy") choices))]
               [d (in-list (remove* (list b l) choices))]
               [t (in-list (remove* (list b l d) choices))])
     (list b l d t))))

(define how-many-schedules
  (length schedules))

(define (schedule-of-time t)
  (list-ref schedules
            (modulo (date-year-day t)
                    how-many-schedules)))

(module+ main
  (require web-server/servlet-env
           web-server/http)

  (define how-many-days 7)
  (define days
    (vector "Sunday"
            "Monday"
            "Tuesday"
            "Wednesday"
            "Thursday"
            "Friday"
            "Saturday"))

  (define (start req)
    (define ts
      (for/list ([i (in-range how-many-days)])
        (seconds->date (+ (current-seconds) (* 24 60 60 i)))))
    (define these-schedules
      (for/list ([t (in-list ts)])
        (schedule-of-time t)))
    (response/xexpr
     `(html
       (head
        (title "Prayer Chart")
        (style #<<END
          table tr td:nth-child(1) {
                                    font-weight: bold;
                                                 text-align: right;
                                                 }
END
          ))
       (body
        (table
         (thead
          (th "Occasion")
          ,@(for/list ([t (in-list ts)])
              `(th ,(vector-ref days (date-week-day t)))))
         (tbody
          (tr (td "Breakfast")
              ,@(map (compose tdize first) these-schedules))
          (tr (td "Lunch")
              ,@(map (compose tdize second) these-schedules))
          (tr (td "Dinner")
              ,@(map (compose tdize third) these-schedules))
          (tr (td "Bed-time")
              ,@(map (compose tdize fourth) these-schedules))))))))

  (serve/servlet
   start
   #:listen-ip #f
   #:command-line? #t
   #:servlet-regexp #rx""
   #:port 9005))
