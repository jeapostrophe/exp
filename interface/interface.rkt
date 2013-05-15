#lang racket
(require "contract-in.rkt"
         racket/contract
         racket/require-syntax
         racket/provide-syntax)

(begin-for-syntax
  (struct interface (spec)))
(define-syntax (define-interface stx)
  (syntax-case stx ()
    [(_ interface-id
        [id id/c]
        ...)
     (syntax/loc stx
       (define-syntax interface-id
         (interface #'([id id/c] ...))))]))

(define-require-syntax (interface-in stx)
  (syntax-case stx ()
    [(_ interface-id mod-path)
     (let ()
       (with-syntax
           ([([id id/c] ...)
             (interface-spec (syntax-local-value #'interface-id))])
         (syntax/loc stx
           (contract-in mod-path
                        [id id/c]
                        ...))))]))

(define-provide-syntax (interface-out stx)
  (syntax-case stx ()
    [(_ interface-id)
     (let ()
       (with-syntax
           ([([id id/c] ...)
             (interface-spec (syntax-local-value #'interface-id))])
         ;; xxx this is invalid because contract-out is a pre-transformer
         (syntax/loc stx
           (contract-out [id id/c]
                         ...))
         ;; xxx this doesn't do anything... where did it go? macro
         ;; stepper doesn't show it
         (syntax-local-lift-module-end-declaration
          (syntax/loc stx
            (provide/contract [id id/c] ...)))
         (syntax/loc stx
           ;; xxx just get the names
           (combine-out id ...))))]))

(provide define-interface
         interface-in
         interface-out)
