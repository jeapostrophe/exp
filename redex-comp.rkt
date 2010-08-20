#lang racket
;; Compiler
(require (for-syntax syntax/parse
                     racket
                     unstable/syntax
                     "redex-comp-help.rkt"))
(provide define-nonterminal
         nt:number nt:hole)

(define (nt:number stx) #'XXX)
(define (nt:hole stx) #'XXX)

(define-for-syntax (extract-nonterminals nts pat)
  (syntax-parse
   pat
   #:literals ([number nt:number #:phase 0]
               [hole nt:hole #:phase 0])
   [i:id #:when (memf (curry free-identifier=? #'i) nts)
         (list pat)]
   [number (list pat)]
   [hole 
    (record-disappeared-uses (list pat))
    empty]
   [(p ...)
    (apply append
           (syntax-map (curry extract-nonterminals nts)
                       #'(p ...)))]
   [_ empty]))

#;(define-for-syntax (compile-match-pattern sexpr->this this-id nts fs pat)
    (let loop ([pat pat])
      (syntax-parse
       pat
       #:literals ([number nt:number #:phase 0]
                   [hole nt:hole #:phase 0])
       [i:id #:when (free-identifier=? this-id #'i)
             (match-define (cons f1 fr) fs)
             (set! fs fr)
             (quasisyntax/loc pat
               (app #,sexpr->this #,f1))]
       [number 
        (match-define (cons f1 fr) fs)
        (set! fs fr)
        (quasisyntax/loc pat
          (? number? #,f1))]
       [hole
        ; XXX
        empty]
       [(p ...)
        (quasisyntax/loc pat
          (list #,@(syntax-map loop #'(p ...))))]
       [_ 
        (syntax/loc pat
          'pat)])))

(define-syntax (define-nonterminal stx)
  (syntax-case stx ()
    [(_ #;sexpr->nt:id
        (nt:id fv:id ...)
        pat ...)
     (with-disappeared-uses
         (begin
           (record-disappeared-uses (syntax->list #'(fv ...)))
           (with-syntax* ([(v ...) (generate-temporaries #'(pat ...))]
                          [((f ...) ...)
                           (syntax-map (λ (v)
                                         (define nts (extract-nonterminals (syntax->list #'(nt fv ...)) v))
                                         (record-disappeared-uses nts)
                                         (generate-temporaries 
                                          nts))
                                       #'(pat ...))]
                          #;[(mpat ...)
                             (syntax-map (λ (v fs)
                                           (compile-match-pattern #'sexpr->nt #'nt (syntax->list #'(fv ...)) fs v))
                                         #'(pat ...)
                                         #'((f ...) ...))])
             (syntax/loc stx
               (begin
                 (struct nt ())
                 (struct v nt (f ...))
                 ...
                 (define sexpr->nt
                   (match-lambda
                     [mpat (v f ...)]
                     ...))
                 
                 
                 )))))]))