#lang racket/base
(require (for-syntax racket/base
                     typed-racket/utils/tc-utils))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ module (output ...))
     (with-syntax
         ([(fake-output ...)
           (generate-temporaries #'(output ...))])
       (syntax/loc stx
         (#%plain-module-begin
          (begin-for-syntax
            (set-box! typed-context? #t))
          (require module)
          (define fake-output
            output)
          ...
          (provide
           (rename-out
            [fake-output output]
            ...)))))]))

(provide
 (rename-out
  [module-begin #%module-begin]))
