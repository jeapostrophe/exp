#lang scheme
(require (for-syntax syntax/parse
                     scheme
                     unstable/syntax)
         (planet jaymccarthy/spvector))

(define-syntax (define-semipersitent-struct stx)
  (syntax-parse 
   stx
   [(_ type:id (field:id ...))
    (with-syntax*
        ([semi-type (generate-temporary #'type)]
         [semi-type-v (format-id #'semi-type "~a-v" #'semi-type)]
         [make-semi-type (format-id #'semi-type "make-~a" #'semi-type)]
         [make-type (format-id stx "make-~a" #'type)]
         [(type-field ...) (syntax-map (curry format-id stx "~a-~a" #'type) #'(field ...))]
         [(set-type-field ...) (syntax-map (curry format-id stx "set-~a-~a" #'type) #'(field ...))]
         [(field-i ...) (build-list (length (syntax->list #'(field ...))) (λ (x) x))])
      (syntax/loc stx
        (begin
          (define-struct type (field ...)
            #:omit-define-values)
          (define-struct semi-type (v))
          (define (make-type field ...)
            (make-semi-type (make-spvector field ...)))
          (define (type-field st)
            (spvector-ref (semi-type-v st) field-i))
          ...
          (define (set-type-field st v)
            (make-semi-type
             (spvector-set (semi-type-v st) field-i v)))
          ...)))]))

;; Example
(require tests/eli-tester)
(define-semipersitent-struct kons (car cdr))

(define a (make-kons 1 2))
(define ap (set-kons-car a 3))
(test
 (kons-car a) => 1
 (kons-car ap) => 3)
