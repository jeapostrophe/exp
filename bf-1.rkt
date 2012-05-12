#lang racket

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

;; In response to: http://stackoverflow.com/questions/10560124
(define parse
  (match-lambda
   [(list* 'lbr more)
    (define-values (more-p pipe-in) (pipe (parse more)))
    (list* (pipe-in (list)) (parse more-p))]
   [(list* 'rbr more)
    (pipe-out more)]
   [(list) 
    (list)]
   [(list* i more)
    (list* i (parse more))]))

(require rackunit)
(check-equal? (parse '())  '())
(check-equal? (parse '(>)) '(>))
(check-equal? (parse '(> >)) '(> >))
(check-equal? (parse '(lbr > > rbr)) '((> >)))
(check-exn exn:fail? (λ () (parse '(lbr > >))))
(check-equal? (parse '(> lbr > > rbr >)) '(> (> >) >))

;; Plus, a puzzle...
(define (A i)
  (cond
    [(zero? i)
     empty]
    [else
     (define-values (j pipe-in) (pipe (list* i (A (pipe-out (sub1 i))))))
     (list* j (pipe-in (sub1 j)))]))
;; Can you predict what this expression evaluates to?
(A 10)
