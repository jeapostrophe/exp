#lang racket

(struct program () #:transparent)
(struct instruction program (which rest) #:transparent)
(struct control program (inner rest) #:transparent)
(struct halt program () #:transparent)

(define more-box (make-parameter #f))
(define (return-to-lbr i l)
  (set-box! (more-box) l)
  i)
(define (wait-for-rbr l)
  (define this-more-box (box #f))
  (define i 
    (parameterize ([more-box this-more-box])
      (parse l)))
  (values i (unbox this-more-box)))

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
(check-equal? (parse '(> lbr > > rbr >)) 
              (instruction '>
                           (control (instruction '> (instruction '> (halt)))
                                    (instruction '> (halt)))))
