#lang racket/base
(require racket/match
         racket/function
         racket/list
         (prefix-in ru: rackunit)
         syntax/parse/define
         (for-syntax racket/base
                     syntax/parse))

(struct res:exn (x))
(struct res:values (vs))
(define (res-equal? x y)
  (or (and (res:values? x) (res:values? y)
           (equal? (res:values-vs x)
                   (res:values-vs y)))
      (and (res:exn? x) (res:exn? y)
           (equal? (exn-message (res:exn-x x))
                   (exn-message (res:exn-x y))))))

(define-syntax-rule (->values e)
  (with-handlers ([exn? (λ (x) (res:exn x))])
    (call-with-values (λ () e)
      (λ vs (res:values vs)))))

(define-syntax-rule (check-equal? x y)
  (ru:check res-equal? (->values x) (->values y)))
(define-syntax-rule (check-not-equal? x y)
  (ru:check (negate res-equal?) (->values x) (->values y)))
(define-syntax-rule (check-not-false x)
  (let ()
    (define xv (->values x))
    (cond
      [(res:values? xv)
       (define len (length (res:values-vs xv)))
       (if (= len 1)
         (ru:check-not-false (first (res:values-vs xv)))
         (ru:check-not-equal? len 1))]
      [else
       (ru:check-pred res:values? xv)])))
(define-syntax-rule (check-false x)
  (let ()
    (define xv (->values x))
    (cond
      [(res:values? xv)
       (define len (length (res:values-vs xv)))
       (if (= len 1)
         (ru:check-false (first (res:values-vs xv)))
         (ru:check-not-equal? len 1))]
      [else
       (ru:check-pred res:exn? xv)])))

(define (exn-match x b)
  (match b
    [(? string? s)
     (exn-match x (regexp (regexp-quote s)))]
    [(? regexp? r)
     (regexp-match r (exn-message x))]
    [(? procedure? okay?)
     (okay? x)]))

(define-syntax-rule (check-exn a b)
  (ru:check-exn
   (λ (x) (exn-match x b))
   (λ () a)))
(define-syntax-rule (check-not-exn a b)
  (let ()
    (define av (->values a))
    (if (res:exn? av)
      (ru:check-false (exn-match (res:exn-x av) b))
      (ru:check-pred res:values? av))))

(begin-for-syntax
  (define-splicing-syntax-class test
    #:attributes (unit fail-unit)
    [pattern (~seq #:f t:test)
             #:attr unit #'t.fail-unit
             #:attr fail-unit #'t.unit]
    [pattern (~seq #:t a:expr)
             #:attr unit
             (syntax/loc #'a
               (check-not-false a))
             #:attr fail-unit
             (syntax/loc #'a
               (check-false a))]
    [pattern (~seq #:exn a:expr b:expr)
             #:attr unit
             (syntax/loc #'a
               (check-exn a b))
             #:attr fail-unit
             (syntax/loc #'a
               (check-not-exn a b))]
    [pattern (~seq a:expr b:expr)
             #:attr unit
             (syntax/loc #'a
               (check-equal? a b))
             #:attr fail-unit
             (syntax/loc #'a
               (check-not-equal? a b))]
    [pattern (~seq a:expr)
             #:with (c:test) (syntax/loc #'a (#:t a))
             #:attr unit #'c.unit
             #:attr fail-unit #'c.fail-unit]))

(define-simple-macro (chk e:test ...)
  (begin e.unit ...))

(module+ test
  (chk
   1 1
   #:f 1 0
   #:f #:f #:f 1 0
   #:f #:f 1 1
   #:f (/ 1 0) +inf.0
   (/ 1 0) (/ 1 0)
   #:f (error 'xxx "a") (error 'xxx "b")

   #:f #:t (/ 1 0)
   #:t (values 0 1)
   #:t (values #f 1)
   #:f #:t (values #f 1)

   1 1
   2 2
   #:exn (/ 1 0) "division"
   #:exn (/ 1 0) #rx"di.ision"
   #:f #:exn (/ 1 1) "division"
   #:f #:exn (/ 1 0) "diblision"

   #:t (chk 1)
   #:t 1
   #:f #f
   #:f #:t #f
   1 1
   #:t 1
   #:f 2 3

   (values 1 2) (values 1 2)
   #:f (values 1 2) (values 2 3)
   #:f (values 1 2) 3
   #:f 3 (values 1 2)
   (quotient/remainder 10 3) (values 3 1)))
