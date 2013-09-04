#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/list)
         racket/list)

(begin-for-syntax
  (define-syntax-class formals
    #:attributes ([f 1])
    [pattern rest:id
             #:attr [f 1] (list #'rest)]
    [pattern (mandatory:id . rest:formals)
             #:attr [f 1] (cons #'mandatory (attribute rest.f))]
    [pattern ((~seq mkw:keyword mandatory:id) . rest:formals)
             #:attr [f 1] (cons #'mandatory (attribute rest.f))]
    [pattern ([optional:id default:expr] . rest:formals)
             #:attr [f 1] (cons #'optional (attribute rest.f))]
    [pattern ((~seq okw:keyword [optional:id default:expr]) . rest:formals)
             #:attr [f 1] (cons #'optional (attribute rest.f))]
    [pattern ()
             #:attr [f 1] empty])

  (define-syntax-rule (query-set i v)
    (λ (k d) (if (eq? i k) v d)))
  (define-syntax-rule (query-ref o i d)
    (foldr (λ (f a) (f i a)) d (attribute o)))

  (define-splicing-syntax-class option
    #:attributes (q)
    [pattern (~seq #:accessor-fmt fmt:str)
             #:attr q
             (query-set 'accessor-fmt (syntax->datum #'fmt))]))

(define-syntax (sstruct stx)
  (syntax-parse stx
    [(_ (n:id . h:formals) o:option ...)
     (define accessor-fmt
       (query-ref o.q 'accessor-fmt (string-append (symbol->string (syntax->datum #'n)) "-~a")))
     (with-syntax
         ([n? (format-id #'n "~a?" #'n)]
          [([n-f n-fi] ...)
           (for/list ([f (in-list (attribute h.f))]
                      [fi (in-naturals)])
             (list (format-id f accessor-fmt f)
                   fi))])
       (quasisyntax/loc stx
         (begin
           (define-values (n:type n:constructor n? n:accessor n:mutator)
             (make-struct-type
              'n
              #f
              #,(length (attribute h.f))
              0 #f
              empty
              (current-inspector)
              #f
              empty
              #f
              'n))
           (define (n . h)
             (n:constructor h.f ...))
           (define (n-f n)
             (n:accessor n n-fi))
           ...)))]))

(module+ test
  (require rackunit)

  (let ()
    (sstruct (posn x y))
    (define p0 (posn 1 2))
    (check-true (posn? p0))
    (check-false (posn? 1))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2))

  (let ()
    (sstruct (posn x y)
             #:accessor-fmt "posn.~a")
    (define p0 (posn 1 2))
    (check-equal? (posn.x p0) 1)
    (check-equal? (posn.y p0) 2))

  (let ()
    (sstruct (posn x y [z 3]))
    (define p0 (posn 1 2))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2)
    (check-equal? (posn-z p0) 3)
    (define p1 (posn 1 2 4))
    (check-equal? (posn-x p1) 1)
    (check-equal? (posn-y p1) 2)
    (check-equal? (posn-z p1) 4))

  (let ()
    (sstruct (posn x y [z (+ x y)]))
    (define p0 (posn 1 2))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2)
    (check-equal? (posn-z p0) 3)
    (define p1 (posn 1 2 4))
    (check-equal? (posn-x p1) 1)
    (check-equal? (posn-y p1) 2)
    (check-equal? (posn-z p1) 4))

  (let ()
    (sstruct (posn x #:y y [z (+ x y)]))
    (define p0 (posn 1 #:y 2))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2)
    (check-equal? (posn-z p0) 3)
    (define p1 (posn 1 4 #:y 2))
    (check-equal? (posn-x p1) 1)
    (check-equal? (posn-y p1) 2)
    (check-equal? (posn-z p1) 4))

  (let ()
    (sstruct (posn x #:y y #:z [z (+ x y)]))
    (define p0 (posn 1 #:y 2))
    (check-equal? (posn-x p0) 1)
    (check-equal? (posn-y p0) 2)
    (check-equal? (posn-z p0) 3)
    (define p1 (posn 1 #:z 4 #:y 2))
    (check-equal? (posn-x p1) 1)
    (check-equal? (posn-y p1) 2)
    (check-equal? (posn-z p1) 4)
    (define p2 (posn 1 #:y 2 #:z 4))
    (check-equal? (posn-x p2) 1)
    (check-equal? (posn-y p2) 2)
    (check-equal? (posn-z p2) 4)))
