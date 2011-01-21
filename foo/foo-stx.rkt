#lang racket/base
(require syntax/parse
         (for-template racket/base))
(struct method (id)
        #:property prop:procedure
        (λ (m stx)
          (with-syntax ([m-id (method-id m)])
            (syntax-parse
             stx
             [f:id
              ; XXX keywords
              (syntax/loc stx (λ (obj . args) (apply obj m-id args)))]
             [(f:id obj:expr . args)
              (syntax/loc stx (obj m-id . args))]))))

(provide (struct-out method))