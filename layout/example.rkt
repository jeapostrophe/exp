#lang racket/base
(require (for-syntax racket/base
                     racket/syntax
                     syntax/parse)
         racket/vector
         racket/list)
(module+ test
  (require rackunit/chk))

(begin-for-syntax
  (define-syntax-rule (in-stx-list l)
    (in-list (syntax->list l))))

(define (make-seal name props inspector)
  (define-values (ty make pred acc mut)
    (make-struct-type name #f 1 0 #f props inspector #f (list 0) #f name))
  (values
   make
   pred
   (λ (x) (acc x 0))))

(begin-for-syntax
  (define-syntax-class struct-field
    #:attributes (cpat kw)
    [pattern n:keyword
             #:attr kw #'n
             #:attr cpat (generate-temporary #'n)]
    ;; xxx
    [pattern [ct:expr n:keyword]
             #:attr kw #'n
             #:attr cpat (generate-temporary #'n)]
    ;; xxx
    [pattern [n:keyword #:mutable]
             #:attr kw #'n
             #:attr cpat (generate-temporary #'n)])

  (define-syntax-class struct-option
    ;; xxx
    [pattern #:mutable]))

(define-syntax (struct stx)
  (syntax-parse stx
    [(_ n:id (f:struct-field ...) o:struct-option ...)
     (with-syntax ([(f.idx ...)
                    (for/list ([i (in-naturals)]
                               [f (in-stx-list #'(f ...))])
                      i)]
                   [field-count
                    (length (syntax->list #'(f ...)))])
       (syntax/loc stx
         (begin
           (define-values (seal seal? unseal)
             ;; xxx parent
             ;; xxx pass props
             ;; xxx pass inspector
             (make-seal 'n empty (current-inspector)))
           (define-syntax (n n-stx)
             (define-syntax-class n-kw
               (pattern f.kw
                        #:attr idx #'f.idx)
               ...)
             (syntax-parse n-stx
               [(_ #:? ne:expr)
                (syntax/loc n-stx
                  (seal? ne))]
               [(_ ne:expr nf:n-kw (... ...))
                (syntax/loc n-stx
                  (let ([une (unseal ne)])
                    ;; xxx have nf have a reference attr that knows
                    ;; the offset
                    (values (vector-ref une nf.idx)
                            (... ...))))]
               ;; xxx implement mutability option
               ;; xxx hide ordering?
               [(_ ne:expr (~seq nf:n-kw nf-e:expr) (... ...) #:!)
                (syntax/loc n-stx
                  (let ([une (unseal ne)])
                    ;; xxx here too
                    (vector-set! une nf.idx nf-e)
                    (... ...)))]
               ;; xxx hide ordering?
               [(_ ne:expr (~seq nf:n-kw nf-e:expr) (... ...))
                (syntax/loc n-stx
                  (let* ([une (unseal ne)]
                         [unec (vector-copy une)])
                    ;; xxx and here
                    (vector-set! unec nf.idx nf-e)
                    (... ...)
                    (seal unec)))]
               ;; xxx allow any order
               ;; xxx hide ordering?
               ;; xxx allow optional fields?
               [(_ (~seq (~optional f.kw) (~var f.cpat expr)) ...)
                (syntax/loc n-stx
                  (let ([une (make-vector field-count)])
                    ;; xxx and here
                    (vector-set! une f.idx f.cpat)
                    ...
                    (seal une)))])))))]))

(module+ test
  (define-syntax-rule (check-kons kons)
    (let ()
      (define k (kons 1 2))
      (chk #:t k
           #:t (kons #:? k)
           #:f #:t (kons #:? 1)
           #:f #:t (kons #:? 2)
           (kons (kons #:car 1 #:cdr 2) #:car) 1
           ;; xxx waiting for ~list-any-order
           ;; (kons (kons #:cdr 2 #:car 1) #:car) 1
           (kons k #:car) 1
           (kons k #:cdr) 2
           (kons k #:car #:cdr) (values 1 2)
           (kons k #:cdr #:car) (values 2 1)
           (kons k #:cdr #:car #:cdr) (values 2 1 2)
           ;; xxx only specific order allowed
           ;; (kons #:cdr k) 2
           (kons (kons k #:cdr 3) #:car) 1
           (kons (kons k #:cdr 3 #:car 2) #:cdr #:car) (values 3 2)
           (kons (kons k #:car 2 #:cdr 3) #:cdr #:car) (values 3 2)
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
