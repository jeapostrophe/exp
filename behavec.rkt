#lang racket/load

(module behavec racket
  (require (for-syntax syntax/parse))
  (struct evt (label))
  (struct evt:proj evt (proj-label f))
  (struct evt:call evt:proj (app-label args))
  (struct evt:return evt:call (val))
  (provide (struct-out evt) (struct-out evt:proj)
           (struct-out evt:call) (struct-out evt:return))
  
  (define (monitor-allows? monitor evt)
    (monitor evt))
  ; XXX This should be a form of ->d, but we can't pass information
  ;     from the pre to the post condition
  ;     and we can't generate information at projection time.
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
         (define proj-label (gensym the-base-label))
         (if (first-order? f)
             (if (monitor-allows? the-monitor (evt:proj the-base-label proj-label f))
                 (λ args 
                   (define app-label (gensym the-base-label))         
                   (define args-ctc
                     (map (λ (dom x) (dom x))
                          dom-projs args))
                   (if (monitor-allows? the-monitor (evt:call the-base-label proj-label f app-label args-ctc))
                       (local [(define ans-ctc
                                 (rng-proj 
                                  (apply f args-ctc)))]
                         (if (monitor-allows? the-monitor 
                                              (evt:return the-base-label proj-label f app-label args-ctc ans-ctc))
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
  (provide b->))

(module sort/c racket
  (require 'behavec unstable/match)
  (define (make-sort-monitor)
    (define event-ch (make-channel))
    (thread 
     (λ ()
       (let loop ([evts empty])
         (match-define (vector reply-ch evt) (channel-get event-ch))
         (define new-evts (list* evt evts))
         (define okay-to-call-order?
           (match new-evts
             [(list (evt:call 'order proj _ _ _)
                    _ ...
                    (evt:return 'sort _ _ _ _ _)
                    _ ...
                    (evt:proj 'order proj _)
                    _ ...)
              #f]
             [_
              #t]))
         (define observed-to-not-be-transitive?
           (match new-evts
             [(list (evt:return 'order _ f _ (list c b) #f)
                    _ ...
                    (evt:return 'order _ f _ (list b a) #t)
                    _ ...
                    (evt:return 'order _ f _ (list c a) #f)
                    _ ...)
              #t]
             [_
              #f]))
         (define okay?
           (and okay-to-call-order?
                (not observed-to-not-be-transitive?)))
         (channel-put reply-ch okay?)
         (loop new-evts))))
    event-ch)
  (define the-monitor-ch
    (make-sort-monitor))
  (define (the-monitor evt)
    (define reply-ch (make-channel))
    (channel-put the-monitor-ch (vector reply-ch evt))
    (channel-get reply-ch))
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
      (if (not last-<=)
          (begin (printf "Saving <= for later\n")
                 (set! last-<= <=)
                 <=)
          (begin (printf "Using old <=\n")
                 last-<=)))
    (raw:sort actual-<= l))
  (provide/contract
   [sort sort/c]))

(module sort-client racket
  (require tests/eli-tester
           (prefix-in racket: racket/base)
           (prefix-in good: 'sort)
           (prefix-in bad: 'bad-sort))
  (define good:<= <=)
  (define (bad:<= a b)
    (match* 
     (a b)
           ; We should have...
           ; 0 <= 1 <= 2 | b <= a <= c
           ; But by...
     [(1 0) #f] ; 0 <= 1 | a <= b
     [(2 0) #t] ; 2 <= 0 | c <= a
     [(1 2) #f] ; 2 <= 1 | c <= b
     ))
  (define l (build-list 2 (λ (i) (random 10))))
  (define sorted-l (racket:sort l <=))
  (test
   (good:sort good:<= l) => sorted-l
   (good:sort good:<= l) => sorted-l
   
   (bad:sort good:<= l) => sorted-l
   (bad:sort good:<= l) =error> "disallowed"
   
   (good:sort bad:<= (list 1 0)) => (list 0 1)
   (good:sort bad:<= (list 2 0)) => (list 2 0) ; Remember the sort is broken
   (good:sort bad:<= (list 1 2)) =error> "disallowed" ; But now we know
   ))

(require 'sort-client)