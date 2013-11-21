#lang racket/base
(require (for-syntax racket/base
                     syntax/parse))
(module+ test
  (require rackunit/chk))

(begin-for-syntax
  (define-syntax-class struct-field
    [pattern n:keyword])
  
  (define-syntax-class struct-option))

(define-syntax (struct stx)
  (syntax-parse stx
    [(_ n:id (f:struct-field ...) o:struct-option ...)
     (syntax/loc stx
       (begin 
         (define-syntax (n n-stx)
           (syntax-parse n-stx))))]))

(module+ test
  (define-syntax-rule (check-kons kons)
    (let ()
      (define k (kons 1 2))
      (chk #:t k
           #:t (kons #:? k)
           #:f (kons #:? 1)
           #:f (kons #:? 2)
           (kons (kons #:car 1 #:cdr 2) #:car) 1
           (kons k #:car) 1
           (kons #:cdr k) 2
           (kons (kons k #:cdr 3) #:cdr) 3))))

(module+ test
  (let ()
    (struct kons (#:car #:cdr))
    (check-kons kons)))

(module+ test
  (define-syntax-rule (check-mkons mkons)
    (let ()
      (check-kons mkons)
      (define k (mkons #:car 1 #:cdr 2))
      (define j (mkons k #:car 9))
      (chk (mkons k #:car) 1
           (mkons k #:cdr) 2
           (mkons j #:car) 9
           #:t (mkons k #:car 3 #:!)
           #:t (mkons k #:cdr 4 #:!)
           (mkons j #:car) 9
           (mkons k #:car) 3
           (mkons k #:cdr) 4
           #:t (mkons k #:car 5 #:cdr (mkons k #:car) #:!)
           (mkons j #:car) 9
           (mkons k #:car) 5
           (mkons k #:cdr) 5))))

(module+ test
  (let ()
    (struct mkons (#:car #:cdr) #:mutable)
    (check-mkons mkons)))

(module+ test
  (let ()
    (struct mkons ([#:car #:mutable] [#:cdr #:mutable]))
    (check-mkons mkons)))


(module+ test
  (let ()
    (struct mkons ([_int8 #:car] [_int8 #:cdr]) #:mutable)
    (check-mkons mkons)))
