#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/formlets)

(define link->rank (make-hash))

(define link-formlet
  (formlet
   ,(input-string . => . url)
   url))

(define (add-link req)
  (edit-link req (formlet-process link-formlet req) 1))

(define (edit-link req link inc)
  (hash-update! link->rank link
                (curry + inc) 0)
  (redirect-to "/"))

(define (home req)
  `(html
    (head 
     (title "Rackit"))
    (body
     (h1 "Rackit")
     (form ([action ,(top-url add-link)])
           ,@(formlet-display link-formlet))
     (ol
      ,@(let ()
          (define links
            (sort (hash-keys link->rank)
                  >
                  #:key (curry hash-ref link->rank)))
          (for/list ([l (in-list links)])
            `(li
              (a ([href ,(top-url edit-link l 1)]) "+")
              "/"
              (a ([href ,(top-url edit-link l -1)]) "-")
              " "
              (a ([href ,l]) ,l)
              " "
              ,(format "(~a)" (hash-ref link->rank l)))))))))

(define-values
  (start top-url)
  (dispatch-rules
   [("add") add-link]
   [("edit" (string-arg) (integer-arg)) edit-link]
   [else home]))

(serve/servlet start
               #:servlet-regexp #rx"")