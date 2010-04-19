#lang scheme
(require tests/eli-tester)

(define-syntax (define-pred1 stx)
  (syntax-case stx ()
    [(_ id)
     (with-syntax ([id? (datum->syntax stx (string->symbol (format "~a?" (syntax->datum #'id))))])
       (syntax/loc stx
         (define (id? x) #t)))]))

(define-syntax-rule (define-pred1-wrap i)
  (define-pred1 i))

(define-pred1-wrap x)

(define-syntax (define-pred2 stx)
  (syntax-case stx ()
    [(_ id)
     (with-syntax ([id? (datum->syntax #'id (string->symbol (format "~a?" (syntax->datum #'id))))])
       (syntax/loc stx
         (define (id? x) #t)))]))

(define-syntax-rule (define-pred2-wrap i)
  (define-pred2 i))

(define-pred2-wrap y)

(test
 x? =error> "unbound"
 y?)