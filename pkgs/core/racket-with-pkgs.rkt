#lang racket/base
(require (for-syntax racket/base
                     syntax/strip-context))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ e ...)
     (quasisyntax/loc stx
       (#%module-begin
        #,(replace-context stx #'(require racket/require (path-up "pkg-in.rkt")))
        e ...))]))

(provide (except-out (all-from-out racket/base)
                     #%module-begin)
         (rename-out
          [module-begin #%module-begin]))