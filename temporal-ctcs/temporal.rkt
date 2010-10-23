#lang racket

;; Structs
(struct evt (label))
(struct evt:proj evt (proj-label f))
(struct evt:call evt (proj-label f app-label args))
(struct evt:return evt (proj-label f app-label args vals))
(provide (struct-out evt) (struct-out evt:proj)
         (struct-out evt:call) (struct-out evt:return))

;; Event stream regexp
(define-syntax-rule (evt-regexp evts pat ...)
  (match evts [(list pat ...) #t] [_ #f]))
(provide evt-regexp)

(define (->t* monitor-interpose label)
  (make-contract
   #:name '->t
   #:first-order procedure?
   #:projection
   (λ (b)
     ; XXX Add a monitor setup here?
     (λ (f)
       (define proj-label (gensym label))
       (define f/proj (monitor-interpose b (evt:proj label proj-label f)))
       (if f/proj
           (λ args 
             (define app-label (gensym label))
             (define args/proj (monitor-interpose b (evt:call label proj-label f app-label args)))
             (if args/proj
                 (call-with-values
                  (λ () (apply f/proj args/proj))
                  (λ rets
                    (define rets/proj (monitor-interpose b (evt:return label proj-label f app-label args/proj rets)))
                    (if rets/proj
                        (apply values rets/proj)
                        (raise-blame-error b f "monitor disallowed return with ans ~e" rets))))
                 (raise-blame-error b f "monitor disallowed called with args ~e" args)))
           (raise-blame-error b f "monitor disallowed projection of ~e" f))))))

(define (->t monitor-allows? label . ctcs)
  (define-values (dom-ctcs rng-l) (split-at ctcs (sub1 (length ctcs))))
  (define rng-ctc (first rng-l))
  (define how-many-doms (length dom-ctcs))
  (define (monitor-interpose b evt)
    (match evt
      [(evt:proj label proj f)
       (if (procedure-arity-includes? f how-many-doms)
           (and (monitor-allows? evt)
                f)
           (raise-blame-error b f "expected a function of ~a argument(s), got: ~e" how-many-doms f))]
      [(evt:call label proj f app args)
       (and (monitor-allows? evt)
            (for/list ([ctc (in-list dom-ctcs)]
                       [arg (in-list args)])
              (define proj ((contract-projection ctc) (blame-swap b)))
              (proj arg)))]
      [(evt:return label proj f app args (list ret))
       (define rng-proj ((contract-projection rng-ctc) b))
       (and (monitor-allows? evt)
            (list (rng-proj ret)))]))
  (->t* monitor-interpose label))

(provide ->t*
         ->t)