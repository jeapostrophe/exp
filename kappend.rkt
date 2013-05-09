#lang racket

(struct our-kons (car cdr) #:transparent)
(struct our-kappend (left right) #:transparent)

(define count 0)
(define (kons x y)
  (set! count (add1 count))
  (our-kons x y))
(define (kappend x y)
  (set! count (add1 count))
  (our-kappend x y))

(define our-car
  (match-lambda
   [(our-kons a d) a]
   [(our-kappend x _)
    (our-car x)]))
(define our-cdr
  (match-lambda
   [(our-kons a d) d]
   [(our-kappend x y)
    (our-cdr (On-append x y))]))

;; O(n) in x
(define (On-append x y)
  (if (empty? x)
    y
    (kons (our-car x) (append (our-cdr x) y))))

(define (append x y)
  (if (empty? x)
    y
    (kappend x y)))

(define (first-map f l)
  (if (empty? l)
    empty
    (kons (f (our-car l))
          (map f (our-cdr l)))))

(define (map f l)
  (if (empty? l)
    empty
    (if (our-kappend? l)
      (append (map f (our-kappend-left l))
              (map f (our-kappend-right l)))
      (kons (f (our-car l))
            (map f (our-cdr l))))))

(module+ main
  (define x (kons 1 (kons 2 (kons 3 empty))))
  count
  (define y (kons 4 (kons 5 (kons 6 empty))))
  count
  (define xy (append x y))
  count
  (map add1 xy)
  count)
