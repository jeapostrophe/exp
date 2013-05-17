#lang racket/base
(require rackunit
         racket/list
         racket/match
         racket/stxparam
         (for-syntax racket/base
                     racket/syntax
                     racket/list
                     syntax/parse))

(define-syntax-parameter stack
  (λ (stx) (raise-syntax-error 'stack "Illegal outside rorth" stx)))

(struct stack-op (f))

(begin-for-syntax
  (define (generate-n-temporaries stx)
    (generate-temporaries
     (build-list (syntax->datum stx) (λ (i) stx))))

  (define (generate-n-ids&reverse stx)
    (define l (generate-n-temporaries stx))
    (values l (reverse l)))

  (define-syntax-class stack-spec
    #:attributes ([in_0 1] [in_n 1]
                  [out_0 1] [out_n 1])
    (pattern (input:nat (~datum --) output:nat)
             #:do [(define-values (in_0s in_ns)
                     (generate-n-ids&reverse #'input))
                   (define-values (out_0s out_ns)
                     (generate-n-ids&reverse #'output))]
             #:attr [in_0 1] in_0s
             #:attr [in_n 1] in_ns
             #:attr [out_0 1] out_0s
             #:attr [out_n 1] out_ns)))

(define-syntax (define/raw-rorth stx)
  (syntax-parse stx
    [(_ name (~optional ss:stack-spec) . body)
     (quasisyntax/loc stx
       (begin
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
         (define (f this-stack)
           (syntax-parameterize
               ([stack (make-rename-transformer #'this-stack)])
             . body))
         (define name (name-struct f))))]))

(define-syntax (define/rorth stx)
  (syntax-parse stx
    [(_ name (~optional ss:stack-spec) body ...+)
     (quasisyntax/loc stx
       (define/raw-rorth name
         #,@(if (attribute ss)
              #'(ss)
              #'())
         (rorth #:stack stack body ...)))]))

(define-syntax (define-rorth stx)
  (syntax-parse stx
    [(_ new-name:id ss:stack-spec name:expr)
     (syntax/loc stx
       (define/raw-rorth new-name ss
         (match-define (list* ss.in_n ... left-over) stack)
         (define-values (ss.out_0 ...) (name ss.in_0 ...))
         (list* ss.out_n ... left-over)))]))

(define (maybe-apply-stack-op e stk)
  (if (stack-op? e)
    ((stack-op-f e) stk)
    (list* e stk)))

(define-syntax (rorth stx)
  (syntax-case stx ()
    [(_ #:stack stk)
     (syntax/loc stx stk)]
    ;; xxx optimize this when stack-op is statically known
    [(_ #:stack stk e)
     (syntax/loc stx (maybe-apply-stack-op e stk))]
    [(_ #:stack stk f m ...)
     (syntax/loc stx (rorth #:stack (rorth #:stack stk f) m ...))]
    [(_ e ...)
     (syntax/loc stx (rorth #:stack empty e ...))]))

(define-syntax (check-rorth stx)
  (syntax-case stx ()
    [(_ (r ...) (a ...))
     (with-syntax
         ([(ar ...) (reverse (syntax->list #'(a ...)))])
       (syntax/loc stx
         (check-equal? (rorth r ...)
                       (list ar ...))))]))

(define/raw-rorth :dup (1 -- 2)
  (match-define (list* top rest) stack)
  (list* top top rest))
(define/raw-rorth :drop (1 -- 2)
  (match-define (list* top rest) stack)
  rest)
(define/raw-rorth :swap (2 -- 2)
  (match-define (list* a b rest) stack)
  (list* b a rest))
(define/raw-rorth :rot (3 -- 3)
  (match-define (list* a b c rest) stack)
  (list* c a b rest))
(define/raw-rorth :over (2 -- 3)
  (match-define (list* a b rest) stack)
  (list* b a b rest))
(define/raw-rorth :tuck (2 -- 3)
  (match-define (list* a b rest) stack)
  (list* a b a rest))
(define/raw-rorth :pick
  (match-define (list* i rest) stack)
  (list* (list-ref rest i) rest))

(define-rorth :+ (2 -- 1) +)
(define-rorth :- (2 -- 1) -)
(define-rorth :* (2 -- 1) *)

(provide define/rorth
         define-rorth
         rorth
         check-rorth
         :pick :tuck :over :rot :drop :dup :+ :- :* :swap)
