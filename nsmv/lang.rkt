#lang racket/base
(require racket/stxparam
         racket/splicing
         (for-syntax racket/base
                     racket/syntax
                     racket/list))

(begin-for-syntax
  (define local-state empty)
  (define local-state-fs empty))

(define-syntax-rule (define-invocation-local-state id init)
  (begin
    (begin-for-syntax
      (set! local-state
            (cons
             #'(id init)
             local-state)))
    (define-syntax-parameter id
      (λ (stx) (raise-syntax-error 'id "Local state" stx)))))

(define-syntax-rule
  (define-invocation-local-state-dependent-function (f . args) . body)
  (begin
    (begin-for-syntax
      (set! local-state-fs
            (cons
             #'(f args body)
             local-state-fs)))
    (define-syntax-parameter f
      (λ (stx) (raise-syntax-error 'f "Local state" stx)))))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ . body)
     (with-syntax*
         ([((local-state-id local-state-init) ...)
           local-state]
          [((local-f local-f-args local-f-body) ...)
           local-state-fs]
          [(local-f-new-id ...)
           (generate-temporaries #'(local-f ...))]
          [(local-state-new-id ...)
           (generate-temporaries #'(local-state-id ...))])
       (syntax/loc stx
         (#%module-begin
          (define local-state-new-id local-state-init)
          ...
          (splicing-syntax-parameterize
           ([local-state-id (make-rename-transformer #'local-state-new-id)]
            ...)
           (define (local-f-new-id . local-f-args) . local-f-body)
           ...)
          (splicing-syntax-parameterize
           ([local-f (make-rename-transformer #'local-f-new-id)]
            ...)
           (begin . body)))))]))

(define-invocation-local-state state null)
(define-invocation-local-state-dependent-function (add v)
  (set! state (cons v state)))
(define-invocation-local-state-dependent-function (get)
  state)

(provide (except-out (all-from-out racket/base)
                     #%module-begin)
         (rename-out [module-begin #%module-begin])
         add get)
