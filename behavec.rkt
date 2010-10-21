#lang racket/load

(module behavec racket
  (require (for-syntax syntax/parse))
  (define current-monitors (make-parameter empty))
  (define (monitor-allows? monitor evt)
    (define reply-ch (make-channel))
    (channel-put monitor (vector reply-ch evt))
    (channel-get reply-ch))
  (define (b-> make-monitor . ctcs)
    (define-values (dom-ctcs rng-l) (split-at ctcs (sub1 (length ctcs))))
    (define rng-ctc (first rng-l))
    (define how-many-doms (length dom-ctcs))
    (define first-order?
      (λ (x) (and (procedure? x) (procedure-arity-includes? x how-many-doms))))
    (make-contract
     #:name 'b->
     #:first-order
     first-order?
     #:projection
     (λ (b)
       (define dom-projs 
         (map (λ (dom)
                ((contract-projection dom) (blame-swap b)))
              dom-ctcs))
       (define rng-proj
         ((contract-projection rng-ctc) b))
       (λ (f)
         (if (first-order? f)
             (let ()
               (define-values (this-monitor this-label) (make-monitor))
               (λ args 
                 (parameterize ([current-monitors (list* (vector this-monitor this-label) (current-monitors))])
                   (define args-ctc
                     (map (λ (dom x) (dom x))
                          dom-projs args))
                   (if (monitor-allows? this-monitor (list this-label 'call args-ctc))
                       (local [(define ans-ctc
                                 (rng-proj 
                                  (apply f args-ctc)))]
                         (if (monitor-allows? this-monitor (list this-label 'return args-ctc ans-ctc))
                             ans-ctc
                             (raise-blame-error
                              b f
                              "monitor disallowed return with args ~e and ans ~e" args-ctc ans-ctc)))
                       (raise-blame-error
                        (blame-swap b) f
                        "monitor disallowed called with args ~e" args-ctc)))))
             (raise-blame-error
              b f
              "expected a function of ~a argument(s), got: ~e"
              how-many-doms f))))))
  (provide b->
           current-monitors))

(module sort/c racket
  (require 'behavec)
  (define (make-sort-monitor sort-label)
    (define event-ch (make-channel))
    (thread 
     (λ ()
       (let loop ([evts empty])
         (match-define (vector reply-ch evt) (channel-get event-ch))
         (define okay?
           (match evt
             #;[(list 'order 'return (list a c) a<=c?)
                ...]
             ; Order should not return after sort
             [(list (cons 'order _) 'return _ _)
              #;(printf "Got evt ~a with evts ~e\n" evt evts)
              (not (ormap (match-lambda [(list (cons 'sort _) 'return _ _) #t] [else #f]) evts))]
             [else
              #t]))
         (channel-put reply-ch okay?)
         (loop (list* evt evts)))))
    event-ch)
  (define sort/c
    (b-> (λ ()
           (define label (cons 'sort (gensym 'sort)))
           (printf "New sort monitor: ~a\n" label)
           (values (make-sort-monitor label)
                   label))
         (b-> (λ ()
                (match-define (vector monitor monitor-label)
                              (first (current-monitors)))
                (printf "Connecting order to monitor ~a\n" monitor-label)
                (define label (list* 'order (gensym 'order) monitor-label))
                (values monitor
                        label))
              any/c any/c boolean?)
         (listof any/c)
         (listof any/c)))
  (provide sort/c))

(module raw-sort racket
  (define (insert <= e l)
    (cond
      [(empty? l)
       (list e)]
      [(<= e (first l))
       (list* e l)]
      [else
       (list* (first l)
              (insert <= e (rest l)))]))
  (define (sort <= l)
    (if (empty? l)
        empty
        (insert <= (first l)
                (sort <= (rest l)))))
  (provide sort))

(module sort racket
  (require 'sort/c 'raw-sort)
  (provide/contract
   [sort sort/c]))

(module bad-sort racket
  (require 'sort/c (prefix-in raw: 'raw-sort))
  (define last-<= #f)
  (define (sort <= l)
    (define actual-<=
      (if last-<=
          (begin (printf "Using old <=\n")
                 last-<=)
          (begin (printf "Saving <= for later\n")
                 (set! last-<= <=)
                 <=)))
    (raw:sort actual-<= l))
  (provide/contract
   [sort sort/c]))

(module sort-client racket
  (require tests/eli-tester
           (prefix-in racket: racket/base)
           (prefix-in good: 'sort)
           (prefix-in bad: 'bad-sort))
  (define (good:<= a b) (<= a b))
  (define (bad:<= a b)
    (if (zero? (random 2))
        #f
        (<= a b)))
  (define l (build-list 10 (λ (i) (random 10))))
  (define sorted-l (racket:sort l <=))
  (test
   (good:sort good:<= l) => sorted-l
   (good:sort good:<= l) => sorted-l
   (good:sort bad:<= l) =error> "disallowed"
   
   (bad:sort good:<= l) => sorted-l
   (bad:sort good:<= l) =error> "disallowed"
   (bad:sort bad:<= l) =error> "disallowed"))

(require 'sort-client)