#lang racket/base
(require rackunit
         racket/list
         (for-syntax racket/base
                     syntax/parse))

(begin-for-syntax
  (define-syntax-class stack-spec
    #:attributes (how-many-before how-many-after)
    (pattern (before:id ... (~datum --) after:id ...)
             #:attr how-many-before (datum->syntax #f (length (syntax->list #'(before ...))))
             #:attr how-many-after (length (syntax->list #'(after ...))))))

(define-syntax (define/rorth stx)
  (syntax-parse stx
    [(_ name:id sp:stack-spec body ...)
     #'(define (name stack)
         (apply values (rorth/stack stack body ...)))]))

(define-syntax (define-rorth stx)
  (syntax-parse stx
    [(_ name:id sp:stack-spec new-name:id)
     #'(define (new-name stack)
         (define-values (left-over before) (split-at stack 'sp.how-many-before))
         (call-with-values (λ () (apply name before))
           (λ (after)
             (append left-over after))))]))

(define-syntax-rule (rorth . body)
  (rorth/stack . body))

(define-syntax (rorth/stack stx)
  (syntax-parse stx
    [(_ stk:expr r:expr ...+)
     #'(error 'rorth "~e" '(stk r ...))]))

(define-syntax-rule (check-rorth (r ...) (a ...))
  (check-equal? (call-with-values (λ () (rorth r ...))
                  (λ l l))
                (list a ...)))

(provide define/rorth
         define-rorth
         rorth
         check-rorth)
