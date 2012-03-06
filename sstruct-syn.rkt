#lang racket
(require syntax/parse
         racket/struct-info
         racket/match/patterns)

(define (separate-keywords stx)
  (let loop ([ids empty]
             [kws empty]
             [stx stx])
    (syntax-parse
     stx
     [(kw:keyword arg:id . rst)
      (loop ids (list* (list #'kw #'arg) kws) #'rst)]
     [(arg:id . rst)
      (loop (list* #'arg ids) kws #'rst)]
     [()
      (values (reverse ids) kws)])))

(define-struct sstruct-description 
  (match-xform set-xform 
   struct-type-id super-type-desc
   constructor-id predicate-id
   field-names 
   field-accessors field-mutators
   by-pos-field-names
   by-kw-fields
  formals)
  #:property prop:set!-transformer (struct-field-index set-xform)
  #:property prop:match-expander (struct-field-index match-xform)
  #:property prop:struct-info
  (lambda (sd)
    (define super-type-desc
      (sstruct-description-super-type-desc sd))
    (define super-type-struct-type-id
      (if super-type-desc
          (sstruct-description-struct-type-id super-type-desc)
          #t))
    (list (sstruct-description-struct-type-id sd)
          (sstruct-description-constructor-id sd)
          (sstruct-description-predicate-id sd)
          (reverse (syntax->list (sstruct-description-field-accessors sd)))
          (reverse (sstruct-description-field-mutators sd))
          super-type-struct-type-id)))

(define-syntax-class id-maybe-super
  #:attributes (name parent-desc)
  #:description "identifier or identifier and super"
  (pattern name:id
           #:attr parent-desc #f)
  (pattern (name:id parent)
           #:declare parent (static sstruct-description? "struct description")
           #:attr parent-desc (attribute parent.value)))

(define-syntax-class field-name+options
  #:attributes (name mutable? accessor mutator default-value)
  #:description "field specification"
  (pattern name:id
           #:attr mutable? #f
           #:attr accessor #f
           #:attr mutator #f
           #:attr default-value #f)
  (pattern (name:id 
            (~or (~optional (~and (~bind [mutable? #t])
                                  #:mutable)
                            #:too-many "redundant #:mutable specification in field"
                            #:defaults ([mutable? #f]))
                 (~optional (~seq #:accessor accessor:id)
                            #:too-many "too many #:accessor specifications in field"
                            #:defaults ([accessor #f]))
                 (~optional (~seq #:mutator mutator:id)
                            #:too-many "too many #:mutator specifications in field"
                            #:defaults ([mutator #f]))
                 (~optional default-value:expr
                            #:too-many "too many default value specifications in field"
                            #:defaults ([default-value #f])))
            ...)))

(define-splicing-syntax-class field
  #:attributes (kw name mutable? accessor mutator default-value)
  #:description "field specification"
  (pattern (~seq kw:keyword name+options:field-name+options)
           #:attr name #'name+options.name
           #:attr mutable? (attribute name+options.mutable?)
           #:attr accessor (attribute name+options.accessor)
           #:attr mutator (attribute name+options.mutator)
           #:attr default-value (attribute name+options.default-value))
  (pattern name+options:field-name+options
           #:attr kw #f
           #:attr name #'name+options.name
           #:attr mutable? (attribute name+options.mutable?)
           #:attr accessor (attribute name+options.accessor)
           #:attr mutator (attribute name+options.mutator)
           #:attr default-value (attribute name+options.default-value)))

(provide (all-defined-out))
