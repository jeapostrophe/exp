#lang racket/load

(module behavec racket
  (require (for-syntax syntax/parse))
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
  
  (define (b->* monitor-interpose label)
    (make-contract
     #:name 'b->
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
                          (raise-blame-error (blame-swap b) f "monitor disallowed return with ans ~e" rets))))
                   (raise-blame-error b f "monitor disallowed called with args ~e" args)))
             (raise-blame-error b f "monitor disallowed projection of ~e" f))))))
    
  (define (b-> monitor-allows? label . ctcs)
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
    (b->* monitor-interpose label))
  (provide b->))

(module sort/c racket
  (require 'behavec unstable/match)
  (define (make-sort-monitor)
    (define evts empty)
    (define this-monitor
      (λ (evt)
        (set! evts (list* evt evts))
        (not
         (or 
          ; Are we returning from order after a return from sort, where we previously projected this
          ; order?
          (evt-regexp evts
                      (evt:call 'order proj _ _ _) _ ...
                      (evt:return 'sort _ _ _ _ _) _ ...
                      (evt:proj 'order proj _) _ ...)
          ; Is there a witness that the order is not transitive?
          (evt-regexp evts
                      (evt:return 'order _ f _ (list c b) (list #f)) _ ...
                      (evt:return 'order _ f _ (list b a) (list #t)) _ ...
                      (evt:return 'order _ f _ (list c a) (list #f)) _ ...)))))
    this-monitor)
  (define sort-monitor
    (make-sort-monitor))
  (define sort/c
    (b-> sort-monitor 'sort
         (b-> sort-monitor 'order
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