#lang racket/base
(require (for-syntax racket/base
                     racket/list
                     syntax/parse
                     syntax/id-table
                     racket/dict)
         racket/list
         racket/match)

(struct sys (unknowns constraints))
(struct constraint (name form))
(struct unknown ())

(define (env-ref env n)
  (hash-ref env n 0))

(begin-for-syntax
  (define (remove-stx-duplicates stx)
    (define SEEN (make-free-id-table))
    (for ([i (in-list (syntax->list stx))])
      (dict-set! SEEN i #t))
    (dict-keys SEEN)))

(define-syntax (system stx)
  (syntax-parse stx
    [(_
      #:unknowns un:id ...
      #:constraints ((~literal =) n:id form:expr) ...)
     ;; xxx ensure uns and ns don't overlap
     (with-syntax
         ([(n* ...)
           (remove-stx-duplicates #'(un ... n ...))])
       (syntax/loc stx
         (sys (list 'un ...)
              (list (constraint
                     'n
                     (λ (env)
                       (let ([n* (env-ref env 'n*)] ...)
                         form)))
                    ...))))]))

(struct state (env unknowns constraints) #:transparent)

(define (step st)
  (match-define (state env unknowns constraints) st)
  (define env-p
    (for/fold ([env env])
        ([u (in-list unknowns)])
      (hash-update env u add1 0)))
  (state env-p unknowns constraints))

(define (solved? st)
  (match-define (state env unknowns constraints) st)
  (define-values (env-p final-solved? final-score)
    (for/fold ([env env] [solved? #t] [score 0])
        ([c (in-list constraints)])
      (match-define (constraint name form) c)
      (define current (env-ref env name))
      (define should-be (form env))
      (define diff (abs (- current should-be)))
      (define this-solved? (<= diff 0.01))
      '
      (unless this-solved?
        (eprintf "~a should be ~v but is ~v\n" name should-be current))
      (values (hash-set env name should-be)
              (and solved? this-solved?)
              (+ score diff))))
  (values (state env-p unknowns constraints)
          final-solved?
          final-score))

(define (step-until best-score best-st st)
  (define-values (st-p st-solved? st-score) (solved? st))
  (cond
    [st-solved?
     (state-env st-p)]
    [(< best-score st-score)
     (state-env best-st)]
    [else
     (define st-pp (step st-p))
     (if (< st-score best-score)
       (step-until st-score st st-pp)
       (step-until best-score best-st st-pp))]))

(define (solve a-sys)
  (match-define (sys unknowns constraints) a-sys)
  (define initial-st (state (hasheq) unknowns constraints))
  (step-until +inf.0 #f initial-st))

(define (render env)
  (for ([(k v) (in-hash env)])
    (printf "~a: ~v\n" k v)))

(module+ main
  (render
   (solve
    (system
     #:unknowns
     IMPROVEMENTS
     #:constraints
     (= BUY-PRICE 290000)
     (= BUY-COSTS (+ 7000 11500))
     (= SELL-COSTS% 0.06)
     (= SELL-COSTSk 3000)
     (= MULTIPLIER 2.5)
     (= SELL-PRICE
        (+ BUY-PRICE
           (* MULTIPLIER IMPROVEMENTS)))
     (= PROCEEDS
        0)
     (= PROCEEDS
        (- SELL-PRICE
           BUY-PRICE
           BUY-COSTS
           IMPROVEMENTS
           (* SELL-PRICE SELL-COSTS%)
           SELL-COSTSk))
     (= LIST-PRICE
        (* SELL-PRICE 1.10))))))
