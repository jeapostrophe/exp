#lang racket/base
(require (for-syntax racket/base
                     racket/syntax))

(define-syntax (define-enum stx)
  (syntax-case stx ()
    [(_ class (element ...))
     (with-syntax ([(class-element ...)
                    (for/list ([e (in-list (syntax->list #'(element ...)))])
                      (format-id #'class "~a-~a" #'class e))])
       (syntax/loc stx
         (begin (define class-element (gensym 'class-element))
                ...)))]))

(define-enum colour (red blue green))

colour-red
colour-blue
colour-green
