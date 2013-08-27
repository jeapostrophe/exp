#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/vector)
         racket/list
         racket/match)

(begin-for-syntax
  (define-syntax-rule (in-stx-list e)
    (in-list (syntax->list e))))

(begin-for-syntax
  (struct field-static-info (kw mutable?))

  (define-splicing-syntax-class fmap
    ;; xxx ensure no duplicates
    (pattern (~seq (~seq f:keyword e:expr) ...)
             #:attr hash
             (for/hasheq ([f (in-stx-list #'(f ...))]
                          [e (in-stx-list #'(e ...))])
                         (values (syntax->datum f) e))))

  (struct record-details (fields field->idx))

  (define (record-static-info-fields rsi)
    (record-details-fields (record-static-info-details rsi)))
  (define (record-static-info-field->idx rsi)
    (record-details-field->idx (record-static-info-details rsi)))

  (struct
   record-static-info
   (name
    type constructor predicate accessor mutator
    details)
   #:property prop:match-expander
   (λ (rsi match-stx)
     (syntax-parse match-stx
       [(_ margs:fmap)
        (with-syntax ([name (record-static-info-name rsi)])
          (syntax/loc match-stx
            (and (? (λ (x) (name #:? x)))
                 (app (λ (x) (name x margs.f)) margs.e)
                 ...)))]))
   #:property prop:procedure
   (λ (rsi name-stx)
     (syntax-parse name-stx
       ;; Identification
       [(_ #:? o:expr)
        (quasisyntax/loc name-stx
          (#,(record-static-info-predicate rsi) o))]
       ;; Constructor
       [(_ cargs:fmap)
        ;; xxx check for totality
        (quasisyntax/loc name-stx
          (#,(record-static-info-constructor rsi)
           #,@(for/list ([f (in-vector (record-static-info-fields rsi))])
                (define fkw (field-static-info-kw f))
                (hash-ref (attribute cargs.hash) fkw
                          (λ () (error 'name:constructor "missing value of field ~e in ~e" fkw #'cargs))))))]
       ;; Accessor
       [(_ o:expr fkw:keyword)
        (quasisyntax/loc name-stx
          (#,(record-static-info-accessor rsi)
           o
           #,(hash-ref
              (record-static-info-field->idx rsi)
              (syntax->datum #'fkw)
              (λ ()
                (error 'name:accessor "unknown field ~e\n" 'fkw)))))]
       ;; Updater
       [(_ o:expr uargs:fmap)
        (quasisyntax/loc name-stx
          (let ([oi o])
            (#,(record-static-info-constructor rsi)
             #,@(for/list ([f (in-vector (record-static-info-fields rsi))]
                           [i (in-naturals)])
                  (define fkw (field-static-info-kw f))
                  (hash-ref (attribute uargs.hash) fkw
                            (λ ()
                              (quasisyntax/loc name-stx
                                (#,(record-static-info-accessor rsi)
                                 oi
                                 #,i))))))))]
       ;; Mutator
       [(_ o:expr margs:fmap #:!)
        (with-syntax ([mutator (record-static-info-mutator rsi)]
                      [(margs.f.idx ...)
                       (for/list ([f (in-stx-list #'(margs.f ...))])
                         (hash-ref
                          (record-static-info-field->idx rsi)
                          (syntax->datum f)
                          (λ ()
                            (error 'name:mutator "unknown field ~e\n" f))))])
          (syntax/loc name-stx
            (let ([oi o])
              (mutator oi margs.f.idx margs.e)
              ...)))])))

  (define field-static-info->mutable
    (λ (fsi) (field-static-info (field-static-info-kw fsi) #t)))
  
  (define-syntax-class field-option
    #:attributes (transform)
    (pattern #:mutable
             #:attr transform field-static-info->mutable))

  (define-syntax-class record-field
    #:attributes (info)
    ;; xxx ensure kw is not #:? or #:!
    (pattern kw:keyword
             #:attr info (field-static-info (syntax->datum #'kw) #f))
    (pattern [kw:keyword o:field-option ...]
             #:attr info
             (foldr
              (λ (e a) (e a))
              (field-static-info (syntax->datum #'kw) #f)
              (attribute o.transform))))

  (define-syntax-class record-option
    #:attributes (transform)
    (pattern #:mutable
             #:attr
             transform
             (λ (rd)
               (record-details (vector-map field-static-info->mutable (record-details-fields rd))
                               (record-details-field->idx rd))))))

(define-syntax (record stx)
  (syntax-parse stx
    [(_ name:id (f:record-field ...) o:record-option ...)
     (define finfos (list->vector (attribute f.info)))
     (define rd
       (foldr
        (λ (e a) (e a))
        (record-details
         finfos
         (for/hasheq ([fi (in-vector finfos)]
                      [i (in-naturals)])
                     (values (field-static-info-kw fi) i)))
        (attribute o.transform)))
     (quasisyntax/loc stx
       (begin
         (define-values
           (name:type name:constructor name:predicate name:accessor name:mutator)
           (make-struct-type
            'name
            ;; xxx super type
            #f
            #,(vector-length (record-details-fields rd))
            0
            #f
            ;; xxx properties
            empty
            ;; xxx inspector
            (current-inspector)
            ;; xxx proc-spec
            #f
            (list
             #,@(for/list ([f (in-vector (record-details-fields rd))]
                           [i (in-naturals)]
                           #:unless (field-static-info-mutable? f))
                  i))
            #f
            'name))
         (define-syntax name
           (record-static-info
            #'name
            #'name:type #'name:constructor #'name:predicate #'name:accessor #'name:mutator
            #,rd))))]))

(provide record)

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
    (posn p0 #:x 2 #:!)
    (check-equal? (posn p0 #:x) 2))

  (let ()
    ;; Whole record is mutable
    (record posn (#:x #:y) #:mutable)

    (define p0 (posn #:x 1 #:y 3))
    (check-equal? (posn p0 #:x) 1)
    (check-equal? (posn p0 #:y) 3)
    (posn p0 #:x 2 #:!)
    (posn p0 #:y 4 #:!)
    (check-equal? (posn p0 #:x) 2)
    (check-equal? (posn p0 #:y) 4)
    (posn p0 #:x 1 #:y 3 #:!)
    (check-equal? (posn p0 #:x) 1)
    (check-equal? (posn p0 #:y) 3))

  ;; xxx super
  ;; xxx inspector
  ;; xxx properties
  ;; xxx transparent
  ;; xxx prefab
  ;; xxx methods
  ;; xxx auto
  ;; xxx how to get constructor, predicate, and accessor as function
  ;; xxx guards & contracts
  ;; xxx close records for export
  )
