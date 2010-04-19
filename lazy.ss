#lang scheme

(define-struct a-promise (thnk))

(define (promise* thnk)
  (make-a-promise thnk))

(define force*
  (match-lambda
    [(and ap (struct a-promise (thnk)))
     (thnk)]
    [v v]))

(provide/contract
 [promise* ((-> any/c) . -> . a-promise?)]
 [force* (any/c . -> . any/c)])