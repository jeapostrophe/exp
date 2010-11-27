#lang racket/base
(require racket/contract)

(struct evt (label) #:transparent)
(struct evt:proj evt (proj-label v) #:transparent)
(struct evt:call evt (proj-label f app-label args) #:transparent)
(struct evt:return evt (proj-label f app-label args rets) #:transparent)

(define (monitor/c monitor-allows? label c)
  (define ctc (coerce-contract 'monitored c))
  (make-contract
   #:name (build-compound-type-name 'monitored label c)
   #:projection
   (λ (b)
     (define proj ((contract-projection ctc) b))
     (λ (x)
       (define proj-label (gensym label))
       (define proj-x (proj x))
       (if (monitor-allows? (evt:proj label proj-label proj-x))
           (if (procedure? proj-x)
               ; XXX Could I specialize for a few arguments/returns?
               (λ args
                 (define app-label (gensym label))
                 (if (monitor-allows? (evt:call label proj-label proj-x app-label args))
                     (call-with-values
                      (λ () (apply proj-x args))
                      (λ rets
                        (if (monitor-allows? (evt:return label proj-label proj-x app-label args rets))
                            (apply values rets)
                            (raise-blame-error b x "monitor disallowed return of ~e" rets))))
                     (raise-blame-error (blame-swap b) x "monitor disallowed call with ~e" args)))
               proj-x)
           (raise-blame-error b x "monitor disallowed after projection of ~e" x))))))

(provide (struct-out evt)
         (struct-out evt:proj)
         (struct-out evt:call)
         (struct-out evt:return)
         monitor/c)