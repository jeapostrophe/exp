#lang racket/base
(require (for-syntax racket/base))
(provide (except-out (all-from-out racket/base)
                     #%module-begin)
         (rename-out [module-begin #%module-begin]))

(define-syntax (module-begin stx)
  (syntax-case stx ()
    [(_ . body)
     (with-syntax
         ([add (datum->syntax stx 'add)]
          [get (datum->syntax stx 'get)])
       (syntax/loc stx
         (#%module-begin
          (define state null)
          (define (add v)
            (set! state (cons v state)))

          (define (get)
            state)

          . body)))]))
