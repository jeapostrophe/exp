#lang racket/base
(require "machine.rkt"
         "re-help.rkt"
         racket/match
         (for-syntax syntax/parse
                     unstable/syntax
                     racket/base
                     "re-help.rkt"
                     "re-compile.rkt"))

(define-syntax-rule (define-re-transformer id lam)
  (define-syntax id (re-transformer lam)))

(define-for-syntax (re-expand stx)
  (syntax-parse
   stx
   #:literals (complement seq union star epsilon nullset dseq)
   [((~and op complement) lhs:expr)
    (quasisyntax/loc stx
      (op #,(re-expand #'lhs)))]
   [((~and op star) lhs:expr)
    (quasisyntax/loc stx
      (op #,(re-expand #'lhs)))]
   [((~and op seq) lhs:expr rhs:expr)
    (quasisyntax/loc stx
      (op #,(re-expand #'lhs) #,(re-expand #'rhs)))]
   [((~and op seq) lhs:expr rest:expr ...)
    (quasisyntax/loc stx
      #,(re-expand #'(op lhs (op rest ...))))]
   [((~and op union) lhs:expr rhs:expr)
    (quasisyntax/loc stx
      (op #,(re-expand #'lhs) #,(re-expand #'rhs)))]
   [((~and op union) lhs:expr rest:expr ...)
    (quasisyntax/loc stx
      #,(re-expand #'(op lhs (op rest ...))))]
   [(~and e (~var transformer (static re-transformer? "re transformer")))
    (record-disappeared-uses (list #'transformer))
    (quasisyntax/loc stx
      #,(re-expand ((re-transformer->re (attribute transformer.value)) #'e)))]
   [(~and e ((~var transformer (static re-transformer? "re transformer")) . _))
    (record-disappeared-uses (list #'transformer))
    (quasisyntax/loc stx
      #,(re-expand ((re-transformer->re (attribute transformer.value)) #'e)))]
   [((~and op dseq) pat:expr rhs:expr)
    (quasisyntax/loc stx
      (op pat #,(re-expand #'rhs)))]
   [_
    stx]))

(define-for-syntax (re-compile stx)
  (syntax-parse
   stx
   [the-re:sre
    (attribute the-re.best)]))

(define-syntax (re stx)
  (with-disappeared-uses
      (syntax-case stx ()
        [(_ the-re)
         (re-compile (re-expand #'the-re))])))

(provide
 complement seq union star epsilon nullset dseq
 define-re-transformer
 re)