#lang racket/base
(require racket/contract)

(struct monitor (label) #:transparent)
(struct monitor:proj monitor (proj-label v) #:transparent)
(struct monitor:call monitor (proj-label f app-label kws kw-args args) #:transparent)
(struct monitor:return monitor (proj-label f app-label kws kw-args args rets) #:transparent)

(define (monitor/c monitor-allows? label c)
  (define ctc (coerce-contract 'monitored c))
  (make-contract
   #:name (build-compound-type-name 'monitored label c)
   #:projection
   (λ (b)
     (define proj ((contract-projection ctc) b))
     (define bs (blame-swap b))
     (λ (x)
       (define proj-label (gensym label))
       (define proj-x (proj x))
       (if (monitor-allows? (monitor:proj label proj-label proj-x))
           (if (procedure? proj-x)
               (make-keyword-procedure
                ; XXX Could I specialize for a few arguments/returns/no kws?
                (λ (kws kw-args . args)
                  (define app-label (gensym label))
                  (if (monitor-allows? (monitor:call label proj-label proj-x app-label kws kw-args args))
                      (call-with-values
                       (λ () (keyword-apply proj-x kws kw-args args))
                       (λ rets
                         (if (monitor-allows? (monitor:return label proj-label proj-x app-label kws kw-args args rets))
                             (apply values rets)
                             (raise-blame-error b x "monitor disallowed return of ~e" rets))))
                      (raise-blame-error bs x "monitor disallowed call with (~e,~e,~e)" kws kw-args args))))
               proj-x)
           (raise-blame-error b x "monitor disallowed after projection of ~e" x))))))

(provide (struct-out monitor)
         (struct-out monitor:proj)
         (struct-out monitor:call)
         (struct-out monitor:return)
         monitor/c)