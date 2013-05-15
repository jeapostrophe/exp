#lang racket
(require racket/require-syntax)
(define-require-syntax (contract-in stx)
  (syntax-case stx ()
    [(_ sub [id id/c] ...)
     (with-syntax
         ([(new-id ...)
           (for/list ([i*c (in-list
                            (map syntax->list
                                 (syntax->list #'([id id/c] ...))))])
             (define id (car i*c))
             (define id/c (cadr i*c))
             ;; xxx This is wrong because we can't bind names from a
             ;; require-syntax
             #;
             (syntax-local-lift-expression
              (quasisyntax/loc id
                (contract #,id/c #,id
                          'pos 'neg)))
             1)])
       (syntax/loc stx
         (only-in sub id ...)))]))
(provide contract-in)
