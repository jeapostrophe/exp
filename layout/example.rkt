#lang racket/base
(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse))
(module+ test
  (require rackunit/chk))

(begin-for-syntax
  (define-syntax-rule (in-stx-list l)
    (in-list (syntax->list l))))

(define (make-seal name props inspector)
  (define-values (ty make pred acc mut)
    (make-struct-type name #f 1 0 #f props inspector #f (list 0) #f name))
  (values
   cons
   pred
   (λ (x) (acc x 0))))

(begin-for-syntax
  (define-syntax-class struct-field
    #:attributes (cpat kw)
    [pattern n:keyword
             #:attr kw #'n
             #:attr cpat (generate-temporary #'n)])

  (define-syntax-class struct-option
    [pattern #:mutable]))

(define-syntax (struct stx)
  (syntax-parse stx
    [(_ n:id (f:struct-field ...) o:struct-option ...)
     (with-syntax ([(f.idx ...)
                    (for/list ([i (in-naturals)]
                               [f (in-stx-list #'(f ...))])
                      i)])
       (syntax/loc stx
         (begin
           (define-values (seal seal? unseal) (make-seal))
           (define-syntax (n n-stx)
             (syntax-parse n-stx
               [(_ ne:expr f.kw)
                (syntax/loc n-stx
                  (vector-ref (unseal ne) f.idx))]
               ...
               [(_ ne:expr f.kw nf:expr #:!)
                (syntax/loc n-stx
                  (vector-set! (unseal ne) f.idx nf))]
               ...
               [(_ (~seq (~optional f.kw) f.cpat) ...)
                (syntax/loc n-stx
                  (seal (vector f.cpat ...)))])))))]))

(module+ test
  (define-syntax-rule (check-kons kons)
    (let ()
      (define k (kons 1 2))
      (chk #:t k
           #:t (kons #:? k)
           #:f (kons #:? 1)
           #:f (kons #:? 2)
           (kons (kons #:car 1 #:cdr 2) #:car) 1
           ;; xxx waiting for ~list-any-order
           ;; (kons (kons #:cdr 2 #:car 1) #:car) 1
           (kons k #:car) 1
           ;; (kons #:cdr k) 2
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
