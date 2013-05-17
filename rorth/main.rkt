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

(define-syntax (define/raw-rorth stx)
  (syntax-parse stx
    [(_ name (~optional (input:nat (~datum --) output:nat)) . body)
     (quasisyntax/loc stx
       (begin
         #,(if (attribute input)
             (with-syntax*
              ([(in_0 ...) (generate-n-temporaries #'input)]
               [(in_n ...) (reverse (syntax->list #'(in_0 ...)))]
               [(out_0 ...) (generate-n-temporaries #'output)]
               [(out_n ...) (reverse (syntax->list #'(out_0 ...)))])
              (syntax/loc stx
                (struct name-struct stack-op ()
                        #:property prop:procedure
                        (λ (so in_0 ...)
                          (match-define (list out_n ...) (f (list in_n ...)))
                          (values out_0 ...)))))
             (syntax/loc stx
               (struct name-struct stack-op ())))
         (define (f this-stack)
           (syntax-parameterize ([stack (make-rename-transformer #'this-stack)])
             . body))
         (define name (name-struct f))))]))

(define-syntax (define/rorth stx)
  (syntax-parse stx
    [(_ name (~optional (input:nat (~datum --) output:nat)) body ...+)
     (quasisyntax/loc stx
       (define/raw-rorth name
         #,@(if (attribute input)
              #'((input -- output))
              #'())
         (rorth/stack stack body ...)))]))

(begin-for-syntax
  (define (generate-n-temporaries stx)
    (generate-temporaries (build-list (syntax->datum stx) (λ (i) stx)))))

(define-syntax (define-rorth stx)
  (syntax-parse stx
    [(_ new-name:id (input:nat (~datum --) output:nat) name:expr)
     (with-syntax*
      ([(in_0 ...) (generate-n-temporaries #'input)]
       [(in_n ...) (reverse (syntax->list #'(in_0 ...)))]
       [(out_0 ...) (generate-n-temporaries #'output)]
       [(out_n ...) (reverse (syntax->list #'(out_0 ...)))])
      (syntax/loc stx
        (define/raw-rorth new-name (input -- output)
          (match-define (list* in_n ... left-over) stack)
          (define-values (out_0 ...) (name in_0 ...))
          (list* out_n ... left-over))))]))

(define-syntax-rule (rorth . body)
  (rorth/stack empty . body))

(define (maybe-apply-stack-op e stk)
  (if (stack-op? e)
    ((stack-op-f e) stk)
    (list* e stk)))

(define-syntax rorth/stack
  (syntax-rules ()
    [(_ stk)
     stk]
    [(_ stk e)
     (maybe-apply-stack-op e stk)]
    [(_ stk f m ...)
     (rorth/stack (rorth/stack stk f) m ...)]))

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
