#lang racket

(struct program () #:transparent)
(struct instruction program (which rest) #:transparent)
(struct control program (inner rest) #:transparent)
(struct halt program () #:transparent)

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
    (halt)]
   [(list* '> more)
    (instruction '> (parse more))]
   [(list* 'rbr more)
    (return-to-lbr
     (halt)
     more)]
   [(list* 'lbr more)
    (define-values (inner more-p) (wait-for-rbr more))
    (control inner (parse more-p))]))

(require rackunit)

(check-equal? (parse '()) 
              (halt))
(check-equal? (parse '(>)) 
              (instruction '> (halt)))
(check-equal? (parse '(> >)) 
              (instruction '> (instruction '> (halt))))
(check-equal? (parse '(lbr > > rbr)) 
              (control (instruction '> (instruction '> (halt)))
                       (halt)))
(check-exn exn:fail?
           (λ () (parse '(lbr > >))))
(check-equal? (parse '(> lbr > > rbr >)) 
              (instruction '>
                           (control (instruction '> (instruction '> (halt)))
                                    (instruction '> (halt)))))
