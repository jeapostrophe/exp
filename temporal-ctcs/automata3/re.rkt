#lang racket/base
(require "machine.rkt"
         "re-help.rkt"
         racket/match
         (for-syntax syntax/parse
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

(define-syntax (re stx)
  (syntax-parse
   stx
   #:literals (complement seq union star epsilon nullset)
   [(_ (complement lhs:expr))
    (syntax/loc stx
      (machine-complement (re lhs)))]
   [(_ (star lhs:expr))
    (syntax/loc stx
      (machine-star (re lhs)))]
   [(_ (seq lhs:expr rhs:expr))
    (syntax/loc stx
      (machine-seq (re lhs) (re rhs)))]
   [(_ (seq lhs:expr rest:expr ...))
    (syntax/loc stx
      (re (seq lhs (seq rest ...))))]
   [(_ (union lhs:expr rhs:expr))
    (syntax/loc stx
      (machine-union (re lhs) (re rhs)))]
   [(_ (union lhs:expr rest:expr ...))
    (syntax/loc stx
      (re (union lhs (union rest ...))))]
   [(_ (~and e (~var transformer (static re-transformer? "re transformer"))))
    (quasisyntax/loc stx
      (re #,((re-transformer->re (attribute transformer.value)) #'e)))]
   [(_ (~and e ((~var transformer (static re-transformer? "re transformer")) . _)))
    (quasisyntax/loc stx
      (re #,((re-transformer->re (attribute transformer.value)) #'e)))]
   [(_ epsilon)
    (syntax/loc stx machine-epsilon)]
   [(_ nullset)
    (syntax/loc stx machine-null)]
   [(_ pat:expr)
    (syntax/loc stx
      (machine (match-lambda [pat machine-epsilon] [_ machine-null])))]))

(define re-accepting? machine-accepting?)
(define re-accepts? machine-accepts?)

(provide
 complement seq union star epsilon nullset
 define-re-transformer
 re
 (rename-out [machine? re?])
 re-accepting?
 re-accepts?)