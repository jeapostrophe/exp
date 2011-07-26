#lang racket/base
(require (for-syntax racket/base))

(define-syntax (pkg-require stx)
  (syntax-case stx ()
    [(_ pkg-pth)
     (with-syntax 
         ([pkg-string 
           (datum->syntax stx (format "../~a/pkg-out.rkt" (symbol->string (syntax->datum #'pkg-pth))))])
       (syntax/loc stx
         (begin
           (require (file pkg-string))
           (provide (all-from-out (file pkg-string))))))]))

(provide
 #%module-begin
 (rename-out
  [pkg-require require]))