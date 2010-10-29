#lang racket

;; Structs
(struct evt (label) #:transparent)
(struct evt:proj evt (proj-label f) #:transparent)
(struct evt:call evt (proj-label f f/proj f-final app-label args) #:transparent)
(struct evt:return evt (proj-label f f/proj f-final app-label args vals) #:transparent)
(provide (struct-out evt) (struct-out evt:proj)
         (struct-out evt:call) (struct-out evt:return))

;; Event stream regexp
(define-syntax-rule (evt-regexp evts pat ...)
  (match evts [(list pat ...) #t] [_ #f]))
(provide evt-regexp)

(define (make-trace-predicate ?)
  (define evts empty)
  (λ (evt)
    (set! evts (cons evt evts))
    (? evts)))
(provide make-trace-predicate)

(define LABELS (make-weak-hasheq))
(define (projection-label v)
  (hash-ref LABELS v #f))

(define (*->t* make-monitor-interpose label)
  (make-contract
   #:name '*->t*
   #:first-order procedure?
   #:projection
   (λ (b)
     ; XXX Add a monitor setup here?
     (λ (f)
       (define monitor-interpose (make-monitor-interpose))
       (define proj-label (gensym label))
       (define f/proj (monitor-interpose b (evt:proj label proj-label f)))
       (if f/proj
           (letrec ([f-final
                     (λ args 
                       (define app-label (gensym label))
                       (define args/proj (monitor-interpose b (evt:call label proj-label f f/proj f-final app-label args)))
                       (if args/proj
                           (call-with-values
                            (λ () (apply f/proj args/proj))
                            (λ rets
                              (define rets/proj (monitor-interpose b (evt:return label proj-label f f/proj f-final app-label args/proj rets)))
                              (if rets/proj
                                  (apply values rets/proj)
                                  (raise-blame-error b f "monitor disallowed return with ans ~e" rets))))
                           (raise-blame-error b f "monitor disallowed called with args ~e" args)))])
             (hash-set! LABELS f-final proj-label)
             f-final)
           (raise-blame-error b f "monitor disallowed projection of ~e" f))))))

(define (->t* monitor-interpose label)
  (*->t* (λ () monitor-interpose) label))

(define (*->t make-monitor-allows? label . ctcs)
  (define-values (dom-ctcs rng-l) (split-at ctcs (sub1 (length ctcs))))
  (define rng-ctc (first rng-l))
  (define how-many-doms (length dom-ctcs))
  (define (make-monitor-interpose)
    (define monitor-allows?
      (make-monitor-allows?))
    (define (monitor-interpose b evt)
      (match evt
        [(evt:proj label proj f)
         (if (procedure-arity-includes? f how-many-doms)
             (and (monitor-allows? evt)
                  f)
             (raise-blame-error b f "expected a function of ~a argument(s), got: ~e" how-many-doms f))]
        [(evt:call label proj f f/proj f-final app args)
         (define args-ctc
           (for/list ([ctc (in-list dom-ctcs)]
                      [arg (in-list args)])
             (define proj ((contract-projection ctc) (blame-swap b)))
             (proj arg)))
         (and (monitor-allows? (evt:call label proj f f/proj f-final app args-ctc))
              args-ctc)]
        [(evt:return label proj f f/proj f-final app args (list ret))
         (define rng-proj ((contract-projection rng-ctc) b))
         (define ret-ctc (list (rng-proj ret)))
         (and (monitor-allows? (evt:return label proj f f/proj f-final app args ret-ctc))
              ret-ctc)]))
    monitor-interpose)
  (*->t* make-monitor-interpose label))

(define (->t monitor-allows? label . ctcs)
  (apply *->t (λ () monitor-allows?) label ctcs))

(provide projection-label
         *->t*
         ->t*
         *->t
         ->t)