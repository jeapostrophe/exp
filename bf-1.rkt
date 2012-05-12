#lang racket

;; In response to: http://stackoverflow.com/questions/10560124

(define pipe-tag (make-continuation-prompt-tag 'pipe))
(define (pipe* f)
  (let/ec esc
    (call-with-continuation-prompt f pipe-tag esc)
    (error 'pipe "did not pipe-out")))
(define-syntax-rule (pipe e ...)
  (pipe* (λ () e ...)))
(define (pipe-out v)
  (call-with-composable-continuation
   (λ (come-back)
     (abort-current-continuation pipe-tag v come-back))
   pipe-tag))

(define parse
  (match-lambda
   [(list)
    (list)]
   [(list* 'rbr more)
    (pipe-out more)
    (list)]
   [(list* 'lbr more)
    (define-values (more-p pipe-in) (pipe (parse more)))
    (define inner (pipe-in))
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
