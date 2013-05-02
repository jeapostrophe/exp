#lang racket/base
(require racket/list
         racket/match
         racket/function
         racket/path
         racket/file
         racket/runtime-path
         racket/dict
         racket/format
         "fusion.rkt"
         (prefix-in data: "data.rkt"))
(module+ test
  (require rackunit))

(define-runtime-path cache-path "/tmp/p4g-cache")
(define (path-sanitize s)
  (regexp-replace* #rx"[^a-zA-Z0-9]" s "_"))
(define (make-cache f-id f)
  (λ args
    (define p
      (apply build-path
             cache-path
             (map (compose path-sanitize ~a)
                  (list* f-id args))))
    (cond
      [(file-exists? p)
       ;; (printf "! ~a\n" p)
       (file->value p)]
      [else
       ;; (printf "? ~a\n" p)
       (define ans (apply f args))
       (make-directory* (path-only p))
       (write-to-file ans p)
       ans])))
(define-syntax-rule (cache! f)
  (let ()
    (define old-f f)
    (set! f (make-cache 'f old-f))))

(struct plan (cost))
(struct double plan (l r))
(struct buy plan ())

(define (insert changed?-box new old)
  (cond
    [(not old)
     (set-box! changed?-box #t)
     new]
    [(< (plan-cost new) (plan-cost old))
     (set-box! changed?-box #t)
     new]
    [else
     old]))

(define (optimize c)
  (define init-persona->plan
    (for/hash ([lp (in-list c)])
      (match-define (list l lc) lp)
      (values l (buy lc))))
  (let loop ([persona->plan init-persona->plan])
    (define changed?-box (box #f))
    (define next
      (for*/fold ([this persona->plan])
          ([(l lp) (in-hash persona->plan)]
           [(r rp) (in-hash persona->plan)])
        (cond
          [(double-fusion l r)
           =>
           (λ (res)
             (define lc (plan-cost lp))
             (define rc (plan-cost rp))
             (define plan (double (+ lc rc) l r))
             (hash-update this res (curry insert changed?-box plan) #f))]
          [else
           this])))
    (if (unbox changed?-box)
      (loop next)
      next)))

(struct lplan (res))
(struct ldouble lplan (l r))
(struct lbuy lplan (c))

(define lplan-cost
  (match-lambda
   [(ldouble _ l r)
    (+ (lplan-cost l)
       (lplan-cost r))]
   [(lbuy _ c)
    c]))

(define (linearize p->p)
  (define (linearize-one p pl)
    (match pl
      [(buy c)
       (lbuy p c)]
      [(double _ l r)
       (ldouble
        p
        (linearize-one! l (hash-ref p->p l))
        (linearize-one! r (hash-ref p->p r)))]))
  (define p->lp (make-hash))
  (define (linearize-one! p pl)
    (hash-ref! p->lp p (λ () (linearize-one p pl))))
  (for/list ([(p pl) (in-hash p->p)])
    (linearize-one! p pl)))

(define lplan-format
  (match-lambda
   [(ldouble res l r)
    (format "[~a@(~a x ~a)]"
            res
            (lplan-format l)
            (lplan-format r))]
   [(lbuy res c)
    (format "B(~a)" res)]))

(define (display-plans p->p)
  (define lps 
    (sort (filter ldouble?
                  (linearize p->p))
          <
          #:key lplan-cost
          #:cache-keys? #t))
  (for ([lp (in-list lps)]
        [i (in-range 10)])
    (printf "~a [~a] <= ~a\n"
            (lplan-res lp)
            (lplan-cost lp)
            (lplan-format lp))))

(module+ main
  (require "current.rkt")
  (define remaining
    (filter (λ (p)
              (not (findf (λ (c) (string=? (first c) (data:persona-name p)))
                          compendium)))
            data:personas))
  (displayln  (~a (~a (length remaining)
                      #:align 'right
                      #:min-width 3)
                  " of "
                  (~a (length data:personas)
                      #:align 'right
                      #:min-width 3)
                  " remaining"))
  (display-plans
   (optimize compendium)))
