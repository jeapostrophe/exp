#lang racket/base
(require racket/list
         racket/match
         racket/function)

(define (tdize v)
  `(td ,v))

(define choices
  (list "Daddy" "Mommy" "Frog" "Peach"))

(define (any-same? l r)
  (ormap equal? l r))
(module+ tests
  (require rackunit)
  (check-equal? (any-same? (list "D" "M" "F" "P")
                           (list "D" "P" "F" "M"))
                #t))

(define (snoc l x)
  (append l (list x)))

(define (insert s l)
  (let/ec esc
    (let loop ([l l])
      (match l
        [(list)
         (list s)]
        [(list lst)
         (if (any-same? s lst)
           (esc #f)
           (list s lst))]
        [(list-rest fst rst)
         (if (any-same? s fst)
           (cons fst (loop rst))
           (cons s l))]))))

(define (optimize il)
  (let loop ([init-result empty]
             [to-insert il])
    (define-values
      (result failed)
      (for/fold ([result init-result]
                 [failed empty])
          ([s (in-list to-insert)])
        (define next-result
          (insert s result))
        (cond
          [next-result
           (values next-result failed)]
          [else
           (values result (cons s failed))])))
    (if (empty? failed)
      result
      (loop result failed))))

(define schedules
  (optimize
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
