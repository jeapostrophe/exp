#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     unstable/syntax
                     unstable/wrapc
                     "foo-stx.rkt")
         racket/stxparam)

(define-syntax (define-method stx)
  (syntax-parse
   stx
   [(_ m:id)
    (syntax/loc stx
      (begin
        (define m-id (gensym 'm))
        (define-syntax m (method #'m-id))))]))
(define-syntax-rule (define-method* m ...)
  (begin (define-method m) ...))

(define-syntax-parameter self 
  (λ (stx) (raise-syntax-error 'self "Used outside object")))
(define mmap-empty (hasheq))
(define mmap-set hash-set)
(define mmap-ref hash-ref)
(define-syntax (mmap stx)
  (syntax-parse
   stx
   #:literals (define)
   [(_ parent-e:expr)
    (syntax/loc stx parent-e)]
   [(_ parent-e:expr
       (define ((~var message (static method? "method")) . fmls) body:expr ...)
       n ...)
    (with-disappeared-uses
        (with-syntax ([m-id (method-id (attribute message.value))])
          (record-disappeared-uses (list #'message))
          (syntax/loc stx
            (mmap (mmap-set parent-e
                            m-id
                            (λ (the-self . fmls)
                              (syntax-parameterize ([self (make-rename-transformer #'the-self)])
                                                   body ...)))
                  n ...))))]))

(struct an-object (mmap)
        #:property prop:procedure
        (make-keyword-procedure
         (λ (kws kw-args ao sel . args)
           (define message-map (an-object-mmap ao))
           (keyword-apply
            (mmap-ref message-map sel 
                      (λ () (error 'object "~a does not understand ~v"
                                   (class ao) sel)))
            kws kw-args
            ao args))))

(define-syntax (object stx)
  (syntax-case stx ()
    [(_ parent m ...)
     (with-syntax ([parent/c
                    (wrap-expr/c #'an-object? #'parent
                                 #:name "the parent argument"
                                 #:context stx)])
       (syntax/loc stx
         (an-object
          (mmap (an-object-mmap parent/c)
                m ...))))]))
(define-syntax-rule (extend m ...)
  (object self m ...))
(define-syntax-rule (update [f e] ...)
  (let ([i e] ...)
    (extend (define (f) i) ...)))

(define-method* identity class)
(define (object%)
  (define me (gensym 'obj))
  (an-object
   (mmap mmap-empty
         (define (class) "object")
         (define (identity) me))))

(provide self
         define-method define-method*
         object extend update
         object% identity class)