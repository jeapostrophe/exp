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

(define not-any-same?
  (match-lambda
   [(list)
    #t]
   [(list lst)
    #t]
   [(list-rest fst (and (list-rest snd snd-rst)
                        fst-rst))
    (and (not (any-same? fst snd))
         (not-any-same? fst-rst))]))
(module+ test
  (check-equal? (not-any-same? empty)
                #t)
  (check-equal? (not-any-same? (list (list 1)))
                #t)
  (check-equal? (not-any-same? (list (list 1) (list 1)))
                #f)
  (check-equal? (not-any-same? (list (list 1) (list 2)))
                #t)
  (check-equal? (not-any-same? (list (list 2) (list 1)))
                #t)
  (check-equal? (not-any-same? (list (list 1) (list 2) (list 1)))
                #t))

(define (insert-everywhere e l)
  (for ([i (in-range (add1 (length l)))])
    (define-values (before after) (split-at l i))
    (yield (append before (list e) after))))
(module+ test
  (define (insert-everywhere/l e l)
    (for/list ([r (in-generator (insert-everywhere e l))])
      r))

  (check-equal? (insert-everywhere/l 1 (list))
                (list (list 1)))
  (check-equal? (insert-everywhere/l 1 (list 1 2 3))
                (list (list 1 1 2 3)
                      (list 1 1 2 3)
                      (list 1 2 1 3)
                      (list 1 2 3 1))))

(define permutations
  (match-lambda
   [(list)
    (yield empty)]
   [(list-rest fst rst)
    (for ([rst-perm (in-generator (permutations rst))])
      (insert-everywhere fst rst-perm))]))
(module+ test
  (define (permutations/l l)
    (for/list ([r (in-generator (permutations l))])
      r))

  (check-equal? (permutations/l empty)
                (list empty))
  (check-equal? (permutations/l (list 1))
                (list (list 1)))
  (check-equal? (permutations/l (list 1 2))
                (list (list 1 2)
                      (list 2 1))))

(define (optimize l)
  (for/or ([rl (in-generator (permutations l))]
           [i (in-naturals)])
    (printf "~a\n" i)
    (not-any-same? rl)))

(module+ main
  (require web-server/servlet-env
           web-server/http)

  (printf "done\n")

  (define schedules
    (optimize
     (for*/list ([b (in-list choices)]
                 [l (in-list (remove* (list b "Daddy") choices))]
                 [d (in-list (remove* (list b l) choices))]
                 [t (in-list (remove* (list b l d) choices))])
       (list b l d t))))

  (printf "really done\n")

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

  (for ([i (in-range 4)])
    (for ([s (in-list (next-schedules))])
      (printf "~a\t" (list-ref s i)))
    (newline))
  (exit 1)

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
