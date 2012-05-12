#lang racket

(define lbr-tag (make-continuation-prompt-tag 'lbr))
(define (return-to-lbr i l)
  (call-with-composable-continuation
   (λ (come-back)
     (abort-current-continuation lbr-tag l come-back))
   lbr-tag)
  i)
(define (wait-for-rbr l)
  (let/ec esc
    (call-with-continuation-prompt
     (λ ()
       (parse l))
     lbr-tag
     (λ (l come-back)
       (esc (come-back) l)))
    (error 'parse "lbr did not have closing rbr")))

(define parse
  (match-lambda
   [(list)
    (list)]
   [(list* 'rbr more)
    (return-to-lbr
     (list)
     more)]
   [(list* 'lbr more)
    (define-values (inner more-p) (wait-for-rbr more))
    (list* inner (parse more-p))]
   [(list* i more)
    (list* i (parse more))]))

(require rackunit)

(check-equal? (parse '())  '())
(check-equal? (parse '(>)) '(>))
(check-equal? (parse '(> >)) '(> >))
(check-equal? (parse '(lbr > > rbr)) '((> >)))
(check-exn exn:fail?
           (λ () (parse '(lbr > >))))
(check-equal? (parse '(> lbr > > rbr >))
              '(> (> >) >))
