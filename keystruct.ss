#lang scheme
(require (for-syntax scheme/match
                     scheme/list
                     scheme/struct-info))

(define-for-syntax (fix-first l)
  (if (first l)
      l
      (rest l)))

(define-syntax (struct-keyword-constructor stx)
  (syntax-case stx ()
    [(_ struct-id)
     (unless (identifier? #'struct-id)
       (raise-syntax-error 'struct-keyword-constructor "Not an identifier" #'struct-id))
     (match
         (syntax-local-value 
          #'struct-id
          (lambda ()
            (raise-syntax-error 'struct-keyword-constructor "Not bound syntax identifier" #'struct-id)))
       [(and (? struct-info?)
             (app extract-struct-info (list descriptor constructor predicate (list accessors-reversed ...) mutators super-type-info)))
        (define accessors (fix-first (reverse accessors-reversed)))
        (with-syntax
            ([formals
              (for/fold ([l empty])
                ([a (in-list accessors-reversed)])
                (if a
                    (list* (string->keyword (symbol->string (syntax-e a))) a l)
                    l))]
             [(field ...) accessors])
          (quasisyntax/loc stx
            (lambda formals
              (#,constructor field ...))))]
       [else
        (raise-syntax-error 'struct-keyword-constructor "Not bound to structure info" #'struct-id)])]))


(provide struct-keyword-constructor)