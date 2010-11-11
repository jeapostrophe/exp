#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/formlets)

(define links empty)

(define link-formlet
  (formlet
   ,(input-string . => . url)
   url))

(define (add-link req)
  (set! links
        (list* (formlet-process link-formlet req)
               links))
  (redirect-to "/"))

(define (home req)
  `(html
    (head 
     (title "Rackit"))
    (body
     (h1 "Rackit")
     (form ([action ,(top-url add-link)])
           ,@(formlet-display link-formlet))
     (ul
      ,@(for/list ([l (in-list links)])
          `(li (a ([href ,l]) ,l)))))))

(define-values
  (start top-url)
  (dispatch-rules
   [("add") add-link]
   [else home]))

(serve/servlet start
               #:servlet-regexp #rx"")