#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     "ror-help.rkt")
         web-server/servlet
         web-server/dispatch
         web-server/formlets
         web-server/servlet-env)

; Racket on Rockets!

(define-syntax (begin-unless-defined stx)
  (syntax-parse
   stx
   [(_ something:id e:expr ...)
    (if (identifier-binding #'something)
        (syntax/loc stx (begin))
        (syntax/loc stx (begin e ...)))]))

(define-syntax (define-defaults stx)
  (syntax-parse 
   stx
   [(_ url:id schema:table-schema)
    (syntax/loc stx
      (begin
        (define-struct schema.struct-id (schema.field ...) #:prefab)
        (define schema.table-id (make-hasheq))
        (begin-unless-defined
          schema.index-id
          (define (schema.index-id req)
            (response/xexpr
             `(html (head (title ,(format "All ~a" schema.path)))
                    (body
                     (p (a ([href ,(url schema.new-id)]) "new"))
                     (ul
                      ,@(for/list ([(id v) (in-hash schema.table-id)])
                          `(li (a ([href ,(url schema.show-id id)])
                                  ,(number->string id))))))))))
        (define (this-formlet schema.field ...)
          (formlet
           (div (p schema.field-string ": "
                   ,{(to-string (required (text-input #:value (string->bytes/utf-8 schema.field)))) . => . schema.field})
                ...)
           (schema.struct-id schema.field ...)))
        (begin-unless-defined
          schema.new-id
          (define (schema.new-id req)
            (define new-formlet
              (this-formlet schema.field-string ...))
            (define new-req
              (send/suspend
               (λ (k-url)            
                 (response/xexpr
                  `(html (head (title ,(format "New ~a" schema.path)))
                         (body 
                          (form ([action ,k-url] [method "post"])
                                ,@(formlet-display new-formlet)
                                (input ([type "submit"] [value "Create"])))))))))
            (define new-id (hash-count schema.table-id))
            (hash-set! schema.table-id
                       new-id
                       (formlet-process new-formlet new-req))
            (redirect-to (url schema.show-id new-id))))
        (begin-unless-defined
          schema.show-id
          (define (schema.show-id req id)
            (define obj (hash-ref schema.table-id id))
            (response/xexpr
             `(html (head (title ,(format "Show ~a #~a" schema.path id)))
                    (body
                     (p schema.field-string ": "
                        ,(schema.field-ref obj))
                     ...
                     (p (a ([href ,(url schema.edit-id id)]) "Edit"))
                     (p (a ([href ,(url schema.index-id)]) "Back to Index")))))))
        (begin-unless-defined
          schema.edit-id
          (define (schema.edit-id req id)
            (define obj (hash-ref schema.table-id id))
            (define edit-formlet
              (this-formlet (schema.field-ref obj) ...))
            (define edit-req
              (send/suspend
               (λ (k-url)            
                 (response/xexpr
                  `(html (head (title ,(format "Edit ~a #~a" schema.path id)))
                         (body 
                          (form ([action ,k-url] [method "post"])
                                ,@(formlet-display edit-formlet)
                                (input ([type "submit"] [value "Save"])))))))))
            (hash-set! schema.table-id
                       id
                       (formlet-process edit-formlet edit-req))
            (redirect-to (url schema.show-id id))))))]))

(define-syntax (define-blast-off! stx)
  (syntax-parse 
   stx
   [(_ (dispatch:id url:id) (index:id)
       schema:table-schema ...)
    (syntax/loc stx
      (begin
        (define-defaults url schema)
        ...
        (define-values (dispatch url)
          (dispatch-rules
           [() index]
           [("") index]
           [(schema.path) schema.index-id]
           ...
           [(schema.path (integer-arg) "show") schema.show-id]
           ...
           [(schema.path (integer-arg) "edit") schema.edit-id]
           ...
           [(schema.path "new") schema.new-id]
           ...))))]))

(define (make-index-fun table-paths)
  (λ (req)
    (response/xexpr
     `(html
       (head (title "Site Index"))
       (body
        (ul
         ,@(for/list ([tp (in-list table-paths)])
             `(li (a ([href ,(format "/~a" tp)]) ,tp)))))))))

(define-syntax (define-index stx)
  (syntax-parse
   stx
   [(_ index:id (schema:table-schema ...))
    (syntax/loc stx
      (define index (make-index-fun '(schema.path ...))))]))

(define-syntax (blast-off! stx)
  (syntax-parse
   stx
   [(_ schema:table-schema ...)
    (with-syntax ([index (datum->syntax stx 'index)])
      (syntax/loc stx
        (begin (begin-unless-defined 
                 index
                 (define-index index (schema ...)))
               (define-blast-off! (start url) (index) schema ...)
               (serve/servlet start
                              #:servlet-path ""
                              #:servlet-regexp #rx""))))]))

(provide blast-off!
         define-blast-off!)