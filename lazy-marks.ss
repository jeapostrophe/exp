#lang scheme

(define-struct a-promise (thnk))

(define mark-tag (make-continuation-prompt-tag 'lazy-marks))

(define (promise* thnk)
  (define-values
    (executed? value)
    (let/cc k
      (values #f (make-a-promise (lambda (go-back) (k #t (lambda () (go-back (thnk)))))))))
  (if executed?
      (value)
      value))

(define force*
  (match-lambda
    [(and ap (struct a-promise (thnk)))
     (call/cc thnk)]
    [v v]))

(provide/contract
 [promise* ((-> any/c) . -> . a-promise?)]
 [force* (any/c . -> . any/c)])