#lang racket
;; Compiler
(require (for-syntax syntax/parse
                     racket
                     racket/syntax
                     syntax/stx
                     unstable/syntax
                     "redex-comp-help.rkt"))
(provide define-nonterminal
         nt:number nt:hole
         sexpr->nt
         (struct-out hole))

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
            (stx-map (curry extract-nonterminals nts)
                     #'(p ...)))]
    [_ empty]))

(define-values (prop:sexpr->nt sexpr->nt? sexpr->nt-ref)
  (make-struct-type-property 'sexpr->nt))

(struct hole ())

(define-syntax (sexpr->nt stx)
  (syntax-parse
      stx
                                        ; XXX
    [(_ i:id)
     (with-syntax ([struct:i (format-id #'i "struct:~a" #'i)])
       (syntax/loc stx
         (if (sexpr->nt? struct:i)
           (sexpr->nt-ref struct:i)
                                        ; XXX
           (error 'sexpr->nt "Not a non-terminal"))))]))

(define-for-syntax (compile-match-pattern nts fs pat)
  (let loop ([pat pat])
    (syntax-parse
        pat
      #:literals ([number nt:number #:phase 0]
                  [hole nt:hole #:phase 0])
      [i:id #:when (memf (curry free-identifier=? #'i) nts)
            (match-define (cons f1 fr) fs)
            (set! fs fr)
            (quasisyntax/loc pat
              (app (sexpr->nt i) #,f1))]
                                        ; XXX other nts
      [number
       (match-define (cons f1 fr) fs)
       (set! fs fr)
       (quasisyntax/loc pat
         (? number? #,f1))]
      [hole
       (syntax/loc pat
         (? hole?))]
      [(p ...)
       (quasisyntax/loc pat
         (list #,@(stx-map loop #'(p ...))))]
      [_
       (quasisyntax/loc pat
         '#,pat)])))

(define-syntax (define-nonterminal stx)
  (syntax-parse stx
    [(_ (nt:id fv:id ...)
        pat ...)
     (with-disappeared-uses
      (begin
        (record-disappeared-uses (syntax->list #'(fv ...)))
        (with-syntax* ([(v ...) (generate-temporaries #'(pat ...))]
                       [((f ...) ...)
                        (stx-map (λ (v)
                                   (define nts (extract-nonterminals (syntax->list #'(nt fv ...)) v))
                                   (record-disappeared-uses nts)
                                   (generate-temporaries
                                    nts))
                                 #'(pat ...))]
                       [(mpat ...)
                        (stx-map (λ (v fs)
                                   (compile-match-pattern
                                    (syntax->list #'(nt fv ...))
                                    (syntax->list fs)
                                    v))
                                 #'(pat ...)
                                 #'((f ...) ...))])
                      (syntax/loc stx
                        (begin
                          (define the-sexpr->nt
                            (match-lambda
                             [mpat (v f ...)]
                             ...
                             [x (error 'nt "Not an ~a: ~e" 'nt x)]))
                          (struct nt ()
                                  #:reflection-name 'nt
                                  #:property prop:sexpr->nt the-sexpr->nt)
                          (struct v nt (f ...)
                                  #:reflection-name 'nt)
                          ...)))))]))
