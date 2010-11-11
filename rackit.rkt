#lang racket
(require web-server/servlet
         web-server/servlet-env
         web-server/formlets
         racket/date)

(struct link (name rank url time))
(define link-date (compose seconds->date link-time))

(define url->link (make-hash))

(define link-formlet
  (formlet
   (#%# ,(input-string . => . name)
        ,(input-string . => . url))
   (link name 0 url (current-seconds))))

(define (add-link req)
  (define l (formlet-process link-formlet req))
  (hash-set! url->link (link-url l) l)
  (edit-link req (link-url l) 1))

(define (edit-link req u inc)
  (hash-update! url->link u
                (λ (l)
                  (struct-copy link l
                               [rank (+ inc (link-rank l))])))
  (redirect-to "/"))

(define (show-links links)
  `(ol
   ,@(for/list ([u (in-list links)])
       (define l (hash-ref url->link u))
       `(li
         (a ([href ,(top-url edit-link u 1)]) "+")
         "/"
         (a ([href ,(top-url edit-link u -1)]) "-")
         " "
         (a ([href ,(link-url l)]) ,(link-name l))
         " "
         ,(format "(~a)" (link-rank l))
         " "
         "at " ,(date->string (link-date l) #t)))))

(define (home req)
  `(html
    (head 
     (title "Rackit"))
    (body
     (h1 "Rackit")
     (form ([action ,(top-url add-link)])
           ,@(formlet-display link-formlet)
           (input ([type "submit"])))
     (h2 "Ranked")
     ,(show-links 
       (sort (hash-keys url->link)
             >
             #:key (compose link-rank (curry hash-ref url->link))))
     (h2 "Time")
     ,(show-links 
       (sort (hash-keys url->link)
             >
             #:key (compose link-time (curry hash-ref url->link)))))))

(define-values
  (start top-url)
  (dispatch-rules
   [("add") add-link]
   [("edit" (string-arg) (integer-arg)) edit-link]
   [else home]))

(serve/servlet start
               #:servlet-regexp #rx"")