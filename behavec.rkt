#lang racket/load

(module behavec racket
  (require (for-syntax syntax/parse))
  (define current-monitors (make-parameter empty))
  (define (monitor-allows? monitor evt)
    (define reply-ch (make-channel))
    (channel-put monitor (vector reply-ch evt))
    (channel-get reply-ch))
  (define (b-> the-monitor the-base-label . ctcs)
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
         (define proj-label (list (gensym the-base-label) the-base-label))
         (if (first-order? f)
             (if (monitor-allows? the-monitor (list proj-label 'proj f))
                 (λ args 
                   (define this-label (cons (gensym the-base-label) proj-label))         
                   (define args-ctc
                     (map (λ (dom x) (dom x))
                          dom-projs args))
                   (if (monitor-allows? the-monitor (list this-label 'call args-ctc))
                       (local [(define ans-ctc
                                 (rng-proj 
                                  (apply f args-ctc)))]
                         (if (monitor-allows? the-monitor (list this-label 'return args-ctc ans-ctc))
                             ans-ctc
                             (raise-blame-error
                              (blame-swap b) f
                              "monitor disallowed return with args ~e and ans ~e" args-ctc ans-ctc)))
                       (raise-blame-error
                        b f
                        "monitor disallowed called with args ~e" args-ctc)))
                 (raise-blame-error
                  b f
                  "monitor disallowed projection of ~e"
                  f))
             (raise-blame-error
              b f
              "expected a function of ~a argument(s), got: ~e"
              how-many-doms f))))))
  (provide b->
           current-monitors))

(module sort/c racket
  (require 'behavec racket/pretty unstable/match)
  (define (make-sort-monitor)
    (define event-ch (make-channel))
    (thread 
     (λ ()
       (let loop ([evts empty])
         (match-define (vector reply-ch evt) (channel-get event-ch))
         (define okay?
           (match evt
             ; Order should not return after sort
             [(list (list application proj 'order) 'return _ _)
              ; Look for a return from sort...
              (define found-a-bad-thing?
                (let sort-loop ([evts evts])
                  (match evts
                    [(list) #f]
                    [(list-rest evt evts)
                     (match evt
                       [(list (list _ _ 'sort) 'return _ _)
                        ; Look for a previous return from this projection of order
                        (let order-loop ([evts evts])
                          (match evts
                            [(list) #f]
                            [(list-rest evt evts)
                             (match evt
                               [(list (list _ (== proj) 'order) 'return _ _)
                                #t]
                               [_
                                (order-loop evts)])]))]
                       [_
                        (sort-loop evts)])])))
              (not found-a-bad-thing?)]
             [else
              #t]))
         #;(unless okay?
           (pretty-print evts))
         (channel-put reply-ch okay?)
         (loop (list* evt evts)))))
    event-ch)
  (define the-monitor
    (make-sort-monitor))
  (define sort/c
    (b-> the-monitor 'sort
         (b-> the-monitor 'order
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
  (define good:<= <=)
  (define bad:<= >=)
  (define l (build-list 2 (λ (i) (random 10))))
  (define sorted-l (racket:sort l <=))
  (test
   (good:sort good:<= l) => sorted-l
   (good:sort good:<= l) => sorted-l
   ;(good:sort bad:<= l) =error> "disallowed"
   
   (bad:sort good:<= l) => sorted-l
   (bad:sort good:<= l) =error> "disallowed"
   ;(bad:sort bad:<= l) =error> "disallowed"
   ))

(require 'sort-client)