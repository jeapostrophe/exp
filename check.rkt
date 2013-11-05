#lang racket/base
(require racket/match
         (prefix-in ru: rackunit)
         (for-syntax racket/base
                     syntax/parse))

(struct res:exn (x) #:transparent)
(struct res:values (vs) #:transparent)

(define-syntax-rule (->values e)
  (with-handlers ([exn? (λ (x) (res:exn x))])
    (call-with-values (λ () e)
      (λ vs (res:values vs)))))

(define-syntax-rule (check-equal? x y)
  (ru:check-equal? (->values x) (->values y)))
(define-syntax-rule (check-not-equal? x y)
  (ru:check-not-equal? (->values x) (->values y)))
(define-syntax-rule (check-not-false x)
  (ru:check-not-false (->values x)))
(define-syntax-rule (check-false x)
  (ru:check-false (->values x)))

(define (exn-match x b)
  (match b
    [(? string?)
     (exn-match x (regexp (regexp-quote b)))]
    [(? regexp?)
     (regexp-match b (exn-message x))]
    [(? procedure?)
     (b x)]))

(define-syntax-rule (check-exn a b)
  (ru:check-exn
   (λ (x) (exn-match x b))
   (λ () a)))
(define-syntax-rule (check-not-exn a b)
  (ru:check-exn
   (λ (x) (not (exn-match x b)))
   (λ () a)))

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

(define-syntax (chk stx)
  (syntax-parse stx
    [(_ e:test ...)
     (syntax/loc stx
       (begin e.unit ...))]))

(define-syntax-rule (checks . b)
  (module+ test (chk . b)))

(checks
 1 1
 #:f 1 0
 #:f #:f 1 1
 #:f (/ 1 0) +inf.0
 (/ 1 0) (/ 1 0)

 1 1
 2 2
 #:exn (/ 1 0) "division"
 #:exn (/ 1 0) #rx"di.ision"
 ;;#:fail #:exn (/ 1 0) "diblision"

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
 (quotient/remainder 10 3) (values 3 1))
