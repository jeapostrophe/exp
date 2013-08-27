#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/list
         racket/match)

(begin-for-syntax
  (define-syntax-rule (in-stx-list e)
    (in-list (syntax->list e))))

(begin-for-syntax
  (define-syntax-class field-option
    (pattern #:mutable))

  (struct field-static-info (kw))

  (define-syntax-class record-field
    #:attributes (info)
    ;; xxx ensure kw is not #:?
    (pattern kw:keyword
             #:attr info #'(field-static-info 'kw))
    (pattern [kw:keyword o:field-option ...]
             #:attr info #'(field-static-info 'kw)))

  (define-syntax-class record-option
    (pattern #:mutable)))

(begin-for-syntax
  (struct
   record-static-info
   (type constructor predicate accessor mutator
         fields)
   #:property prop:match-expander
   (λ (rsi match-stx)
     (syntax-parse match-stx
       [(_ (~seq fkw:keyword fv:expr) ...)
        (syntax/loc match-stx
          (list fv ...))]))
   #:property prop:procedure
   (λ (rsi name-stx)
     (syntax-parse name-stx
       ;; Identification
       [(_ #:? o:expr)
        (quasisyntax/loc name-stx
          (#,(record-static-info-predicate rsi) o))]
       ;; Constructor
       [(_ (~seq fkw:keyword fv:expr) ...)
        ;; xxx ensure no duplicates
        (define fv-map
          (for/hasheq ([fkw (in-stx-list #'(fkw ...))]
                       [fv (in-stx-list #'(fv ...))])
                      (values (syntax->datum fkw) fv)))
        ;; xxx check for totality
        (quasisyntax/loc name-stx
          (#,(record-static-info-constructor rsi)
           #,@(for/list ([f (in-list (record-static-info-fields rsi))])
                (define fkw (field-static-info-kw f))
                (hash-ref fv-map fkw
                          (λ () (error 'name:constructor "missing value of field ~e in ~e" fkw fv-map))))))]
       ;; Accessor
       [(_ o:expr fkw:keyword)
        (quasisyntax/loc name-stx
          (#,(record-static-info-accessor rsi)
           o
           #,(for/or ([f (in-list (record-static-info-fields rsi))]
                      [i (in-naturals)])
               (and (eq? (syntax->datum #'fkw) (field-static-info-kw f))
                    i))))]
       ;; Updater or mutator
       [(_ o:expr (~seq fkw:keyword fv:expr) ...)
        (syntax/loc name-stx
          #f)]))))

(define-syntax (record stx)
  (syntax-parse stx
    [(_ name:id (f:record-field ...) o:record-option ...)
     (quasisyntax/loc stx
       (begin
         (define-values
           (name:type name:constructor name:predicate name:accessor name:mutator)
           (make-struct-type
            'name
            ;; xxx super type
            #f
            #,(length (syntax->list #'(f ...)))
            0
            #f
            ;; xxx properties
            empty
            ;; xxx inspector
            (current-inspector)
            ;; xxx proc-spec
            #f
            ;; xxx immutables
            empty
            #f
            'name))
         (define-syntax name
           (record-static-info
            #'name:type #'name:constructor #'name:predicate
            #'name:accessor #'name:mutator
            (list f.info ...)))))]))

(module+ test
  (require rackunit)

  (let ()
    (record posn (#:x #:y))

    ;; Creation
    (define p0 (posn #:x 1 #:y 3))
    ;; Identification
    (check-true (posn #:? p0))
    (check-false (posn #:? 3))
    ;; Accessor
    (check-equal? (posn p0 #:x) 1)
    (check-equal? (posn p0 #:y) 3)
    ;; Updating
    (define p1 (posn p0 #:x 2))
    (check-equal? (posn p1 #:x) 2)
    (check-equal? (posn p1 #:y) 3)
    (define p2 (posn p0 #:y 4))
    (check-equal? (posn p2 #:x) 1)
    (check-equal? (posn p2 #:y) 4)
    (define p3 (posn p0 #:y 4 #:x 2))
    (check-equal? (posn p3 #:x) 2)
    (check-equal? (posn p3 #:y) 4)

    ;; Matching
    (check-equal? (match p1 [(posn #:x x #:y y) (list x y)])
                  (list 2 3))
    (check-equal? (match p1 [(posn #:y y #:x x) (list x y)])
                  (list 2 3))
    (check-equal? (match p1 [(posn #:x x) (list x 3)])
                  (list 2 3)))

  (let ()
    (record posn ([#:x #:mutable] #:y))

    (define p0 (posn #:x 1 #:y 3))
    (check-equal? (posn p0 #:x) 1)
    ;; Mutation
    (posn p0 #:x! 2)
    (check-equal? (posn p0 #:x) 2))

  (let ()
    ;; Whole record is mutable
    (record posn (#:x #:y) #:mutable)

    (define p0 (posn #:x 1 #:y 3))
    (check-equal? (posn p0 #:x) 1)
    (check-equal? (posn p0 #:y) 3)
    (posn p0 #:x! 2)
    (posn p0 #:y! 4)
    (check-equal? (posn p0 #:x) 2)
    (check-equal? (posn p0 #:y) 4))

  ;; xxx super
  ;; xxx inspector
  ;; xxx properties
  ;; xxx transparent
  ;; xxx prefab
  ;; xxx methods
  ;; xxx auto
  )
