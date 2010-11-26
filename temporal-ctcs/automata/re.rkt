#lang racket/base
(require "machine.rkt"
         "re-help.rkt"
         racket/match
         (for-syntax syntax/parse
                     unstable/syntax
                     racket/base
                     "re-help.rkt"))

(define-syntax-rule (define-re-transformer id lam)
  (define-syntax id (re-transformer lam)))

(define-syntax (nullset stx) (raise-syntax-error 'nullset "Outside re" stx))
(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside re" stx))
(define-syntax (complement stx) (raise-syntax-error 'complement "Outside re" stx))
(define-syntax (seq stx) (raise-syntax-error 'seq "Outside re" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside re" stx))
(define-syntax (star stx) (raise-syntax-error 'star "Outside re" stx))
(define-syntax (dseq stx) (raise-syntax-error 'dseq "Outside re" stx))

(define-syntax (re stx)
  (with-disappeared-uses
      (syntax-parse
       stx
       #:literals (complement seq union star epsilon nullset dseq)
       [(_ ((~and op complement) lhs:expr))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (machine-complement (re lhs)))]
       [(_ ((~and op star) lhs:expr))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (machine-star (re lhs)))]
       [(_ ((~and op seq) lhs:expr rhs:expr))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (machine-seq (re lhs) (re rhs)))]
       [(_ ((~and op seq) lhs:expr rest:expr ...))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (re (seq lhs (seq rest ...))))]
       [(_ ((~and op union) lhs:expr rhs:expr))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (machine-union (re lhs) (re rhs)))]
       [(_ ((~and op union) lhs:expr rest:expr ...))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (re (union lhs (union rest ...))))]
       [(_ (~and e (~var transformer (static re-transformer? "re transformer"))))
        (record-disappeared-uses (list #'transformer))
        (quasisyntax/loc stx
          (re #,((re-transformer->re (attribute transformer.value)) #'e)))]
       [(_ (~and e ((~var transformer (static re-transformer? "re transformer")) . _)))
        (record-disappeared-uses (list #'transformer))
        (quasisyntax/loc stx
          (re #,((re-transformer->re (attribute transformer.value)) #'e)))]
       [(_ (~and op epsilon))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx machine-epsilon)]
       [(_ (~and op nullset))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx machine-null)]
       [(_ ((~and op dseq) pat:expr rhs:expr))
        (record-disappeared-uses (list #'op))
        (syntax/loc stx
          (machine (match-lambda [pat (re rhs)] [_ machine-null])))]
       [(_ pat:expr)
        (syntax/loc stx
          (re (dseq pat epsilon)))])))

(define re-accepting? machine-accepting?)
(define re-accepts? machine-accepts?)
(define re-accepts?/prefix-closed machine-accepts?/prefix-closed)

(provide
 complement seq union star epsilon nullset dseq
 define-re-transformer
 re
 (rename-out [machine? re?])
 re-accepting?
 re-accepts?
 re-accepts?/prefix-closed)