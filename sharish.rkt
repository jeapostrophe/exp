#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/mpair
         racket/list
         racket/match)

(struct placeholder (sealed? value)
        #:transparent
        #:mutable)

(define undefined
  (letrec ([x x]) x))

(define (empty-placeholder)
  (placeholder #f undefined))
(define (placeholder-fill! ph v)
  (when (placeholder-sealed? ph)
    (error 'placeholder-fill! "Cannot fill after seal: ~e" ph))
  (set-placeholder-value! ph v))
(define (placeholder-seal! ph)
  (when (placeholder-sealed? ph)
    (error 'placeholder-seal! "Cannot seal twice: ~e" ph))
  (set-placeholder-sealed?! ph #t))
(define (placeholder-extract ph)
  (unless (placeholder-sealed? ph)
    (error 'placeholder-extract "Cannot extract until sealed ~e" ph))

  (define seen? (make-hasheq))
  (define ans undefined)
  (let loop ([v ph] [fill! (λ (ans-v) (set! ans ans-v))])
    (displayln v)
    (match v
      [(or (? number?) (? boolean?))
       (fill! v)]
      [(mcons a d)
       (define m (mcons undefined undefined))
       (fill! m)
       (loop a (λ (x) (set-mcar! m x)))
       (loop d (λ (x) (set-mcdr! m x)))]
      [(? placeholder?)
       (define first-time? (not (hash-has-key? seen? v)))
       (hash-update! seen? v (λ (more) (cons fill! more)) empty)
       (when first-time?
         (loop (placeholder-value v)
               (λ (final-v)
                 (for ([fill! (in-list (hash-ref seen? v))])
                   (fill! final-v)))))]))
  ans)

(define-syntax (sharish stx)
  (syntax-parse stx
    [(_ ([x:id xe] ...) xb)
     (syntax/loc stx
       (let ([x (empty-placeholder)] ...)
         (begin
           (placeholder-fill! x xe)
           ...
           (placeholder-seal! x)
           ...
           (set! x (placeholder-extract x))
           ...
           xb)))]))

(module+ test
  (require rackunit/chk)

  (struct posn (x y))
  (sharish ([a (mcons  1 x)]
            [b (mcons #t x)]
            [c (mcons  a x)]
            [d (vector a b c d)]
            [e (box d)]
            [f (posn d e)]
            [x (mlist a b c d e f x)])
           
           (chk #:t (eq? 1 (mcar a))
                #:t (eq? x (mcdr a))
                #:t (eq? #t (mcar b))
                #:t (eq? x (mcdr b))
                #:t (eq? a (mcar c))
                #:t (eq? x (mcdr c))
                #:t (eq? a (vector-ref d 0))
                #:t (eq? b (vector-ref d 1))
                #:t (eq? c (vector-ref d 2))
                #:t (eq? d (vector-ref d 3))
                #:t (eq? d (unbox e))
                #:t (eq? d (posn-x f))
                #:t (eq? e (posn-y f))
                #:t (eq? a (mlist-ref x 0))
                #:t (eq? b (mlist-ref x 1))
                #:t (eq? c (mlist-ref x 2))
                #:t (eq? d (mlist-ref x 3))
                #:t (eq? e (mlist-ref x 4))
                #:t (eq? f (mlist-ref x 5))
                #:t (eq? x (mlist-ref x 6)))))
