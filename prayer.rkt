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
  (list "Daddy" "Mommy" "Frog" "Peach" "Hazel"))

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
  (require json
           racket/runtime-path)

  (define schedules
    (optimize
     (for*/list ([l (in-list (remove* (list "Daddy") choices))]
                 [b (in-list (remove* (list l) choices))]
                 [d (in-list (remove* (list b l) choices))]
                 [t (in-list (remove* (list b l d) choices))])
       (list b l d t))))

  (displayln (length schedules))

  (define-runtime-path prayer.json "prayer.json")

  (with-output-to-file prayer.json
    #:exists 'replace
    (λ () 
      (printf "var schedules = \n")
      (write-json schedules)
      (printf ";\n"))))
