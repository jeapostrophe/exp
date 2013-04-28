#lang racket/base
(require racket/list
         racket/match
         racket/path
         racket/file
         racket/runtime-path
         racket/dict
         racket/format
         "fusion.rkt"
         (prefix-in data: "data.rkt"))
(module+ test
  (require rackunit))

(struct plan-double (left right result) #:prefab)
(struct plan-triple (p1 p2 p3 result) #:prefab)

(define (display-plan plan-cost plan)
  (match plan
    [(plan-double (data:persona _ _ l)
                  (data:persona _ _ r)
                  (data:persona _ _ a))
     (printf "Double fusion: ~a x ~a = ~a [~a]\n"
             l r a (plan-cost plan))]
    [(plan-triple (data:persona _ _ p1)
                  (data:persona _ _ p2)
                  (data:persona _ _ p3)
                  (data:persona _ _ a))
     (printf "Triple fusion: (~a x ~a) x ~a = ~a [~a]\n"
             p1 p2 p3 a (plan-cost plan))]))

(define (compendium->plan-cost comp)
  (define (persona-cost p)
    (first (dict-ref comp (data:persona-name p) (list +inf.0))))
  (match-lambda
   [(plan-double l r _)
    (+ (persona-cost l) (persona-cost r))]
   [(plan-triple p1 p2 p3 _)
    (+ (persona-cost p1) (persona-cost p2) (persona-cost p3))]))

(define (double-arcana-pairs t1-a)
  (for/fold ([l empty])
      ([max-a (in-list data:arcana)]
       [max-c (in-list data:fusion-chart)])
    (for/fold ([l l])
        ([low-a (in-list data:arcana)]
         [some-a (in-list max-c)])
      (if (equal? t1-a some-a)
        (list* (cons low-a max-a) l)
        l))))

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
       (printf "! ~a\n" p)
       (file->value p)]
      [else
       (printf "? ~a\n" p)
       (define ans (apply f args))
       (make-directory* (path-only p))
       (write-to-file ans p)
       ans])))
(define-syntax-rule (cache! f)
  (let ()
    (define old-f f)
    (set! f (make-cache 'f old-f))))

(cache! double-arcana-pairs)

(define (double-options t1)
  (match-define (data:persona t1-a t1-l t1-n) t1)
  (for/fold ([l empty])
      ([l-a*r-a (in-list (double-arcana-pairs t1-a))])
    (match-define (cons l-a r-a) l-a*r-a)
    (for*/fold ([l l])
        ([l-p (in-list (hash-ref data:arcana->personas l-a))]
         [r-p (in-list (hash-ref data:arcana->personas r-a))]
         #:when (equal? t1-n
                        (double-fusion (data:persona-name l-p)
                                       (data:persona-name r-p))))
      (list* (plan-double l-p r-p t1) l))))

(cache! double-options)

(define (triple-arcana-pairs t1-a)
  (for/fold ([l empty])
      ([low-a (in-list data:arcana)]
       [low-c (in-list data:fusion-chart)])
    (for/fold ([l l])
        ([max-a (in-list data:arcana)]
         [some-a (in-list low-c)])
      (if (equal? t1-a some-a)
        (list* (cons low-a max-a) l)
        l))))

(cache! triple-arcana-pairs)

(define (triple-options t1)
  (match-define (data:persona t1-a t1-l t1-n) t1)
  (for/fold ([l empty])
      ([int-a*hi-a (in-list (triple-arcana-pairs t1-a))])
    (match-define (cons int-a hi-a) int-a*hi-a)
    (for/fold ([l l])
        ([lo-a*mi-a (in-list (double-arcana-pairs int-a))])
      (match-define (cons lo-a mi-a) lo-a*mi-a)
      (for*/fold ([l l])
          ([p1 (in-list (hash-ref data:arcana->personas lo-a))]
           [p2 (in-list (hash-ref data:arcana->personas mi-a))]
           [p3 (in-list (hash-ref data:arcana->personas hi-a))]
           #:when (equal? t1-n
                          (triple-fusion (data:persona-name p1)
                                         (data:persona-name p2)
                                         (data:persona-name p3))))
        (list* (plan-triple p1 p2 p3 t1) l)))))

(cache! triple-options)

(define (find-minimal-plan plan-cost ts)
  (match ts
    [(list)
     (void)]
    [(list* t1 ts)
     (define options
       (append (double-options t1)
               (triple-options t1)))

     (define best-p
       (and (not (empty? options))
            (argmin plan-cost options)))

     (cond
       [(and best-p (not (= (plan-cost best-p) +inf.0)))
        best-p]
       [else
        (find-minimal-plan plan-cost ts)])]))

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
  (define targets
    (sort (filter (λ (p) (<= (data:persona-lvl p) current-level))
                  remaining)
          <
          #:key data:persona-lvl))
  (define plan-cost
    (compendium->plan-cost
     (append (for/list ([a (in-list active)])
               (list a 0))
             compendium)))
  (display-plan
   plan-cost
   (find-minimal-plan
    plan-cost
    targets)))
