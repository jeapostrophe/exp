#lang racket

(struct lc () #:transparent)
(struct abs lc (var body) #:transparent)
(struct var lc (var) #:transparent)
(struct app lc (rator rand) #:transparent)

(define ex
  '(λ (y)
     ((λ (x) x)
      (λ (x) y))))

(define parse
  (match-lambda
   [(? symbol? s)
    (var s)]
   [`(λ (,var) ,body)
    (abs (parse var) (parse body))]
   [`(,rator ,rand)
    (app (parse rator) (parse rand))]))

(module+ main
  (define ex-p (parse ex))
  ex-p
  (eq? (abs-var ex-p)
       (abs-body (app-rand (abs-body ex-p)))))

(define (new-parse e)
  (define (inner-parse symbol-table e)
    (match e
     [(? symbol? s)
      (hash-ref symbol-table s)]
     [`(λ (,the-var) ,body)
      (define v (var the-var))
      (abs v
           (inner-parse (hash-set symbol-table the-var v) body))]
     [`(,rator ,rand)
      (app (inner-parse symbol-table rator)
           (inner-parse symbol-table rand))]))
  (inner-parse (hasheq) e))

(module+ main
  (define ex-p2 (new-parse ex))
  ex-p2
  (eq? (abs-var ex-p2)
       (abs-body (app-rand (abs-body ex-p2)))))
