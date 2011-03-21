#lang racket
(require tests/eli-tester)

(define (strange-fun f)
  (values number? f))

(test
 (->i ([strategy (predicate?) (-> predicate? any/c)])
      (values [predicate? (-> any/c boolean?)]
              [object any/c]))
 =error>
 "an argument cannot depend on a result")

(define strange/c
  (make-contract
   #:name "amazing contract"
   #:first-order procedure?
   #:projection
   (λ (b)
     (λ (x)
       (λ (f)
         (define ready? #f)
         (letrec-values
             ([(? o) 
               (x 
                (λ (y)
                  (cond
                    [(not ready?)
                     (raise-blame-error b x "cannot call until return")]
                    [(not (? y))
                     (raise-blame-error b x "expected a value of ~a" ?)]
                    [else
                     (f y)])))])
           (set! ready? #t)
           (values ? o)))))))

(define strange-fun/ctc
  (contract strange/c strange-fun 
            'pos 'neg))

(define bad-strange-fun/ctc
  (contract strange/c (λ (f)
                        (f 4)
                        (values number? f))
            'pos 'neg))

(define-values (? o) (strange-fun/ctc (λ (x) x)))
(test
 (o 4) => 4
 (o "string") =error> "contract violation"
 
 (bad-strange-fun/ctc (λ (x) x)) =error> "contract violation")

