#lang racket
;; Compiler
(require (for-syntax syntax/parse
                     racket
                     unstable/syntax
                     "redex-comp-help.rkt"))

(define-syntax (structs stx)
  (syntax-parse
   stx
   [(_ s:id p:id s-any [c:id . c-any] ...)
    (syntax/loc stx
      (begin (struct s p . s-any)
             (struct c s . c-any)
             ...))]))    

(define-syntax (define-language stx)
  (syntax-parse 
   stx
   [(_ lang:id nt:nonterminal-def ...)
    (with-syntax
        ([term:lang (format-unique-id #f #:source #'lang "term:~a" #'lang)]
         [((term:lang:nt 
            (term:lang:nt:v f ...)
            ...)
           ...)
          (map (λ (nt vs) 
                        (list*
                         (format-unique-id #f #:source nt "term:~a:~a" #'lang nt)
                         (map (λ (v) 
                                (list* (format-unique-id #f #:source v "term:~a:~a" #'lang nt)
                                       ; XXX
                                       empty))
                              vs)))
               (attribute nt.id)
               (attribute nt.variants))])
      
      ; XXX Check that nonterminal ids are unique
      (syntax/loc stx
        (begin
          (struct term:lang ())
          (structs term:lang:nt term:lang
                   [()]
                   [term:lang:nt:v (f ...)]
                   ...)
          ...)))]))

(provide (for-syntax num hole)
         define-language)