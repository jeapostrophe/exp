#lang racket
(require (for-syntax syntax/parse
                     racket/match
                     racket/list
                     racket/local
                     racket/dict
                     syntax/id-table
                     racket/syntax
                     unstable/syntax
                     "sstruct-syn.rkt"))

(define-syntax (define-sstruct stx)
  (syntax-parse
   stx
   [(~and
     (_ id:id-maybe-super
       (f:field ...)
       (~or (~optional (~and (~seq #:super (~var super-id (static sstruct-description? "struct description")))
                             (~bind [super (attribute super-id.value)]))
                       #:too-many "too many #:super specifications in struct"
                       #:defaults ([super #f]))
            (~optional (~seq #:constructor constructor:id)
                       #:too-many "too many #:constructor specifications in struct"
                       #:defaults ([constructor #'id.name]))
            (~optional (~seq #:predicate predicate:id)
                       #:too-many "too many #:predicate specifications in struct"
                       #:defaults ([predicate (format-id #'id.name "~a?" #'id.name)]))
            (~optional (~and (~bind [mutable? #t])
                             #:mutable)
                       #:too-many "redundant #:mutable specification in struct"
                       #:defaults ([mutable? #f]))
            (~between (~seq #:property property-type:expr property-value:expr)
                      0 +inf.0)
            (~optional (~seq #:guard guard:expr)
                       #:too-many "too many #:guard specifications in struct"
                       #:defaults ([guard #'#f]))
            (~optional (~or (~seq #:inspector inspector:expr)
                            (~and #:transparent
                                  (~bind [inspector #'#f]))
                            (~and #:prefab
                                  (~bind [inspector #''prefab])))
                       #:too-many "too many #:inspector, #:transparent, #:prefab specifications in struct"
                       #:defaults ([inspector #'(current-inspector)]))
            (~optional (~and #:omit-define-syntaxes
                             (~bind [define-syntaxes? #f]))
                       #:too-many "redundant #:omit-define-syntaxes specification in struct"
                       #:defaults ([define-syntaxes? #t]))
            (~optional (~and #:omit-define-values
                             (~bind [define-values? #f]))
                       #:too-many "redundant #:omit-define-values specification in struct"
                       #:defaults ([define-values? #t])))
       ...)
     (~fail #:when (local [(define field-occurrences
                             (make-bound-id-table))]
                     (for ([f-name (in-list (attribute f.name))])
                       (dict-update! field-occurrences f-name add1 0))
                     (for/or ([(_ how-many) (in-dict field-occurrences)])
                       (how-many . > . 1)))
            "duplicate field identifier")
     (~fail #:when (and (attribute super)
                        (attribute id.parent-desc))
            "redundant #:super specification in struct")
     (~fail #:when (and (equal? ''prefab (syntax->datum #'inspector))
                        (not (empty? (attribute property-type))))
            "cannot use #:property specification for prefab structure type")
     (~fail #:when (and (equal? ''prefab (syntax->datum #'inspector))
                        (not (equal? #f (syntax->datum #'guard))))
            "cannot use #:guard specification for prefab structure type")
     (~fail #:when (and (attribute mutable?)
                        (ormap (λ (x) x) (attribute f.mutable?)))
            "redundant #:mutable specification in field")
     (~fail #:unless (local [(define kws 
                               (map syntax->datum (filter (λ (x) x) (attribute f.kw))))]
                       (equal? kws (remove-duplicates kws)))
            "duplicate keyword in struct")
     (~fail #:when (for/or ([f:mutator (in-list (attribute f.mutator))]
                            [f:mutable? (in-list (attribute f.mutable?))])
                     (and f:mutator
                          (not (or f:mutable? (attribute mutable?)))))
            "illegal #:mutator specification in immutable field"))
    (local [(define parent
              (or (attribute super)
                  (attribute id.parent-desc)))
            (define struct-mutable? (attribute mutable?))
            (define parent-formals
              (if parent
                  (sstruct-description-formals parent)
                  #'()))]
      (with-syntax ([the-constructor (generate-temporary #'constructor)]
                    [super-type-desc (or parent #'#f)]
                    [super-struct-type
                     (if parent
                         (sstruct-description-struct-type-id parent)
                         #f)]
                    [(parent-field-name ...)
                     (if parent
                         (sstruct-description-field-names parent)
                         empty)]
                    [(parent-pos-field-name ...)
                     (if parent
                         (sstruct-description-by-pos-field-names parent)
                         empty)]
                    [((parent-kw-field-kw parent-kw-field-name) ...)
                     (if parent
                         (sstruct-description-by-kw-fields parent)
                         empty)]
                    [(parent-field-accessor ...)
                     (if parent
                         (sstruct-description-field-accessors parent)
                         empty)]
                    ; XXX allow override
                    #;[struct:struct (format-id #'id.name "struct:~a" #'id.name)]
                    [how-many-fields (length (syntax->list #'(f ...)))]
                    [(f-pos ...) (for/list ([i (in-naturals)]
                                            [f (in-list (syntax->list #'(f ...)))])
                                   i)]
                    [(immutable-field-number ...)
                     (for/list ([field-mutable? (in-list (attribute f.mutable?))]
                                [i (in-naturals)]
                                #:when (not (or struct-mutable? field-mutable?)))
                       i)]
                    [(f:accessor ...)
                     (for/list ([accessor (in-list (attribute f.accessor))]
                                [name (in-list (syntax->list #'(f.name ...)))])
                       (or accessor (format-id #'id.name "~a-~a" #'id.name name)))]
                    [(f:mutator-id-or-#f ...)
                     (for/list ([mutator (in-list (attribute f.mutator))])
                       (if mutator
                           (quasisyntax/loc mutator
                             #'#,mutator)
                           #'#f))]
                    [((mutable-f:mutator mutable-f-pos) ...)
                     (for/list ([field-mutable? (in-list (attribute f.mutable?))]
                                [mutator (in-list (attribute f.mutator))]
                                [name (in-list (syntax->list #'(f.name ...)))]
                                [i (in-naturals)]
                                #:when (or struct-mutable? field-mutable?))
                       (list (or mutator (format-id #'id.name "set-~a-~a!" #'id.name name))
                             i))]
                    [(pos-field-name ...)
                     (for/list ([kw (in-list (attribute f.kw))]
                                [name (in-list (attribute f.name))]
                                #:when (not kw))
                       name)]
                    [((kw-field-kw kw-field-name) ...)
                     (for/list ([kw (in-list (attribute f.kw))]
                                [name (in-list (attribute f.name))]
                                #:when kw)
                       (list kw name))]
                    [constructor-formals
                     (for/fold ([formals parent-formals])
                       ([kw (in-list (attribute f.kw))]
                        [name (in-list (attribute f.name))]
                        [default-value (in-list (attribute f.default-value))])
                       (quasisyntax/loc stx
                         (#,@formals
                          #,@(if kw (list kw) empty)
                          #,(if default-value (list name default-value) name))))])
        (syntax/loc stx
          (begin
            (define-values 
              (struct-type struct-constructor struct-predicate struct-accessor struct-mutator)
              (make-struct-type 'id.name
                                super-struct-type
                                how-many-fields
                                0 ; xxx auto fields
                                #f ; xxx auto value
                                (list (cons property-type property-value)
                                      ...)
                                inspector
                                #f ; xxx proc spec
                                (list immutable-field-number ...)
                                guard))
            
            (define the-constructor 
              (lambda constructor-formals
                (struct-constructor parent-field-name ... f.name ...)))
            (define predicate struct-predicate)
            (define (f:accessor s)
              (struct-accessor s f-pos))
            ...
            (define (mutable-f:mutator s v)
              (struct-mutator s mutable-f-pos v))
            ...
            
            (define-syntax constructor
              (make-sstruct-description 
               ; Match expander fields
               (lambda (stx)
                (syntax-case stx ()
                  [(_ . content)
                   (local [(define-values (ids kws) (separate-keywords #'content))]
                     ; xxx remove this hack!
                     (syntax-parse 
                      (list* 'hack kws)
                      [((~or (~datum hack)
                             (~once (parent-kw-field-kw parent-kw-field-name))
                             ...
                             (~once (kw-field-kw kw-field-name))
                             ...)
                        (... ...))
                       (with-syntax ([(parent-pos-field-name ... pos-field-name ...) ids])
                         
                         (syntax/loc stx
                           (? struct-predicate
                              (and (app parent-field-accessor parent-field-name)
                                   ...
                                   (app f:accessor f.name)
                                   ...))))]))]))
               (lambda (stx)
                  (syntax-case stx (set!)
                    [(nm . args) #'(the-constructor . args)]
                    [nm (identifier? #'nm) #'the-constructor]
                    [(set! nm v)
                     (raise-syntax-error #f "struct description cannot be target of a set!" stx)]))
               
               ; Our fields
               
               #'struct-type super-type-desc
               #'the-constructor #'struct-predicate
               #'(f.name ...) 
               #'(f:accessor ...) (list f:mutator-id-or-#f ...)
               #'(parent-pos-field-name ... pos-field-name ...)
               #'((parent-kw-field-kw parent-kw-field-name) ...
                  (kw-field-kw kw-field-name) ...)
               #'constructor-formals))))))]))

(provide define-sstruct)
