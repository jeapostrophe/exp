#lang racket/base
(require rackunit
         racket/list
         racket/match
         (for-syntax racket/base
                     syntax/parse))

(struct stack-op (f))

(begin-for-syntax
  (define (generate-n-temporaries stx)
    (generate-temporaries (build-list (syntax->datum stx) (λ (i) stx))))

  (define-syntax-class stack-nat
    (pattern count:nat
             #:attr [forward 1] (generate-n-temporaries #'count)
             #:attr [backward 1] (reverse (attribute forward))))

  (define-syntax-class stack-spec
    (pattern (input:stack-nat (~datum --) output:stack-nat)
             #:attr [in_0 1] (attribute input.forward)
             #:attr [in_n 1] (attribute input.backward)
             #:attr [out_0 1] (attribute output.forward)
             #:attr [out_n 1] (attribute output.backward))))

(define-syntax (rorthda stx)
  (syntax-parse stx
    [(_ (~or (~seq ss:stack-spec
                   #:lift lifted:expr)
             (~seq (~optional ss:stack-spec)
                   #:lower lstack:id lowered-body:expr ...)
             (~seq (~optional ss:stack-spec)
                   normal-body:expr ...)))
     (with-syntax
         ([body
           (cond
             [(attribute lifted)
              (syntax/loc stx
                (let ()
                  (match-define (list* ss.in_n ... left-over) stack)
                  (define-values (ss.out_0 ...) (lifted ss.in_0 ...))
                  (list* ss.out_n ... left-over)))]
             [(attribute lowered-body)
              (syntax/loc stx
                (begin lowered-body ...))]
             [else
              (syntax/loc stx
                (rorth #:stack stack normal-body ...))])])
       (quasisyntax/loc stx
         (let ()
           #,(if (attribute ss)
               (syntax/loc stx
                 (struct name-struct stack-op ()
                         #:property prop:procedure
                         (λ (so ss.in_0 ...)
                           (match-define
                            (list* ss.out_n ... left-over)
                            (f (list ss.in_n ...)))
                           (values ss.out_0 ...))))
               ;; You can't call Forth functions without a spec.
               (syntax/loc stx
                 (struct name-struct stack-op ())))
           (define (f stack) body)
           (name-struct f))))]))

(define-syntax-rule (define/rorth name . body)
  (define name (rorthda . body)))

(define (maybe-apply-stack-op e stk)
  (if (stack-op? e)
    ((stack-op-f e) stk)
    (list* e stk)))

(define-syntax (rorth stx)
  (syntax-parse stx
    [(_ #:stack stk)
     (syntax/loc stx stk)]
    ;; xxx optimize this when stack-op is statically known
    [(_ #:stack stk e)
     (syntax/loc stx (maybe-apply-stack-op e stk))]
    [(_ #:stack stk f m ...)
     (syntax/loc stx (rorth #:stack (rorth #:stack stk f) m ...))]
    [(_ (~and (~not #:stack) e1) e ...)
     (syntax/loc stx (rorth #:stack empty e1 e ...))]))

(define-syntax (check-rorth stx)
  (syntax-case stx ()
    [(_ (r ...) (a ...))
     (with-syntax
         ([(ar ...) (reverse (syntax->list #'(a ...)))])
       (syntax/loc stx
         (check-equal? (rorth r ...)
                       (list ar ...))))]))

(provide define/rorth
         rorthda
         rorth
         check-rorth)
