#lang racket/base
(require (prefix-in ru: rackunit)
         (for-syntax racket/base
                     syntax/parse))

(define-syntax-rule (check-equal? x y)
  (ru:check-not-exn
   (λ ()
     (ru:check-equal? x y))))

(begin-for-syntax
  (define-splicing-syntax-class test
    #:attributes (unit fail-unit)
    [pattern (~seq #:fail t:test)
             #:attr unit #'t.fail-unit
             #:attr fail-unit #'t.unit]
    [pattern (~seq #:true a:expr)
             #:attr unit
             (syntax/loc #'a
               (check-not-false a))
             #:attr fail-unit
             (syntax/loc #'a
               (check-false a))]
    [pattern (~seq a:expr b:expr)
             #:attr unit
             (syntax/loc #'a
               (check-equal? a b))
             #:attr fail-unit
             (syntax/loc #'a
               (check-not-equal? a b))]
    [pattern (~seq a:expr)
             #:with (c:test) (syntax/loc #'a (#:true a))             
             #:attr unit #'c.unit
             #:attr fail-unit #'c.fail-unit]))

(define-syntax (chk stx)
  (syntax-parse stx
    [(_ e:test ...)
     (syntax/loc stx
       (begin e.unit ...))]))

(module+ test
  (chk 1 1)
  (chk #:fail 1 0)
  (chk #:fail #:fail 1 1)

  (chk #:fail (/ 1 0) +inf.0)
  (chk (/ 1 0) (/ 1 0))

  (chk 1 1
       2 2)

  (chk (/ 1 0) "divide")
  (chk (/ 1 0) #rx"di.ide")

  (chk 1)
  (chk #:true 1)
  (chk #:fail #f)
  (chk #:fail #:true #f)
  (chk 1 1
       #:true 1
       #:fail
       2 3)

  (chk (values 1 2) (values 1 2))
  (chk #:fail (values 1 2) (values 2 3))
  (chk #:fail (values 1 2) 3)
  (chk (quotient/remainder 10 3) (values 3 1)))
