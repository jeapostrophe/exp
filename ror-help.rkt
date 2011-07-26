#lang racket/base
(require racket/syntax
         racket/function
         syntax/parse)
(provide table-schema)

(define (id-syntax->str-syntax i)
  (datum->syntax i (symbol->string (syntax->datum i))))

(define-syntax-class table-schema
  #:description "a table schema"
  (pattern (table-name:id (field-name:id ...))
           #:attr struct-id #'table-name
           #:attr table-id (format-id #'table-name "*~a*" #'table-name)
           #:attr path (id-syntax->str-syntax #'table-name)
           #:attr index-id (format-id #'table-name "~a-index" #'table-name)
           #:attr show-id (format-id #'table-name "~a-show" #'table-name)
           #:attr edit-id (format-id #'table-name "~a-edit" #'table-name)
           #:attr new-id (format-id #'table-name "~a-new" #'table-name)
           #:attr (field-ref 1) (map (curry format-id #'table-name "~a-~a" #'table-name) 
                                  (syntax->list #'(field-name ...)))
           #:attr (field-string 1) (map id-syntax->str-syntax
                                        (syntax->list #'(field-name ...)))
           #:attr (field 1) (syntax->list #'(field-name ...))))