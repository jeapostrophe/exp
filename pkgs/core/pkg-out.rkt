#lang racket/base
(require (for-syntax racket/base
                     racket/list
                     racket/path
                     racket/require-transform)
         racket/require-syntax)

(define-for-syntax (path-directory p)
  (apply build-path (reverse (rest (reverse (explode-path p))))))

(define-syntax (module-provide stx)
  ; XXX If the mod-pth is a require-transformer (i.e. from a required package, pass it through)
  ;     Or have an explicit reprovide
  (syntax-case stx ()
    [(_ mod-pth)
     (with-syntax
         ([mod-string
           (datum->syntax stx (format "~a/~a.rkt"
                                      (path->string (path-directory (syntax-source stx)))
                                      (symbol->string (syntax->datum #'mod-pth))))])
       (syntax/loc stx
         (begin
           (define-require-syntax mod-pth
             (λ (stx)
               (datum->syntax stx
                 '(file mod-string))))
           (provide mod-pth))))]))

(provide
 ; XXX Change to get pkg-in
 #%module-begin
 (rename-out
  [module-provide provide]))