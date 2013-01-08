#lang racket/base
(require racket/list
         racket/match
         racket/function
         racket/generator)
(module+ test
  (require rackunit))

(define (tdize v)
  `(td ,v))

(define choices
  (list "Daddy" "Mommy" "Frog" "Peach"))

(define (any-same? l r)
  (ormap equal? l r))
(module+ test
  (check-equal? (any-same? (list "D" "M" "F" "P")
                           (list "D" "P" "F" "M"))
                #t)
  (check-equal? (any-same? (list "D" "M" "F" "P")
                           (list "F" "D" "P" "M"))
                #f))

(define (insert-everywhere e l)
  (for/list ([i (in-range (add1 (length l)))])
    (define-values (before after) (split-at l i))
    (append before (list e) after)))
(module+ test
  (check-equal? (insert-everywhere 1 (list))
                (list (list 1)))
  (check-equal? (insert-everywhere 1 (list 1 2 3))
                (list (list 1 1 2 3)
                      (list 1 1 2 3)
                      (list 1 2 1 3)
                      (list 1 2 3 1))))

(define (any-same?-distance-data e l)
  (for/list ([x (in-list l)])
    (if (equal? x e)
      'this
      (any-same? e x))))

(define (count-after l)
  (match l
    [(list)
     +inf.0]
    [(list-rest #t more)
     1]
    [(list-rest #f more)
     (add1 (count-after more))]))
(module+ test
  (check-equal? (count-after empty)
                +inf.0)
  (check-equal? (count-after (list #t))
                1)
  (check-equal? (count-after (list #t #f))
                1)
  (check-equal? (count-after (list #f #t #f))
                2))

(define (count-before l)
  (let loop ([cur-min +inf.0]
             [l l])
    (match l
      [(list-rest 'this after)
       (min cur-min (count-after after))]
      [(list-rest #t more)
       (loop 1 more)]
      [(list-rest #f more)
       (loop (add1 cur-min) more)])))
(module+ test
  (check-equal? (count-before (list 'this))
                +inf.0)
  (check-equal? (count-before (list #f 'this))
                +inf.0)
  (check-equal? (count-before (list #f 'this #f))
                +inf.0)
  (check-equal? (count-before (list #t #f 'this #f))
                2.0))

(define (any-same?-distance e l)
  (count-before (any-same?-distance-data e l)))
(module+ test
  (check-equal? (any-same?-distance (list 1)
                                    (list (list 1) (list 2) (list 3)))
                +inf.0)
  (check-equal? (any-same?-distance (list 1 5)
                                    (list (list 1 5) (list 2 6)
                                          (list 3 7) (list 1 4)))
                3.0)
  (check-equal? (any-same?-distance (list 1 4)
                                    (list (list 1 5) (list 2 6)
                                          (list 3 7) (list 1 4)))
                3.0))

(define (insert e l)
  (argmax (curry any-same?-distance e)
          (insert-everywhere e l)))
(module+ test
  (check-equal? (insert (list 1 'x) empty)
                (list (list 1 'x)))
  (check-equal? (insert (list 1 'x) (list (list 1 'y)))
                (list (list 1 'x) (list 1 'y)))
  (check-equal? (insert (list 1 'x) (list (list 1 'y) (list 2 'z)))
                (list (list 1 'y) (list 2 'z) (list 1 'x))))

(define (optimize l)
  (foldl insert empty l))

(module+ main
  (require web-server/servlet-env
           web-server/http)

  (define schedules
    (optimize
     (for*/list ([b (in-list (remove* (list "Daddy") choices))]
                 [l (in-list (remove* (list b) choices))]
                 [d (in-list (remove* (list b l) choices))]
                 [t (in-list (remove* (list b l d) choices))])
       (list b l d t))))

  (define how-many-schedules
    (length schedules))

  (define (schedule-of-time t)
    (list-ref schedules
              (modulo (date-year-day t)
                      how-many-schedules)))

  (define how-many-days 7)
  (define days
    (vector "Sunday"
            "Monday"
            "Tuesday"
            "Wednesday"
            "Thursday"
            "Friday"
            "Saturday"))

  (define (next-times)
    (for/list ([i (in-range how-many-days)])
      (seconds->date (+ (current-seconds) (* 24 60 60 i)))))

  (define (next-schedules)
    (for/list ([t (in-list (next-times))])
      (schedule-of-time t)))

  (define (start req)
    (define ts (next-times))
    (define these-schedules
      (next-schedules))
    (response/xexpr
     `(html
       (head
        (title "Prayer Chart")
        (style
            "table tr td:nth-child(1) {
                                    font-weight: bold;
                                                 text-align: right;
                                                 }"))
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
