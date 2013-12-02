#lang racket/base
(require racket/mpair
         racket/match)

(struct placeholder (extracted? fillers value)
        #:mutable)

(define undefined
  (letrec ([x x]) x))

(define (empty-placeholder)
  (placeholder #f null undefined))
(define (placeholder-fill! ph v)
  (when (placeholder-extracted? ph)
    (error 'placeholder-fill! "Cannot fill after extraction: ~e" ph))
  (set-placeholder-value! ph v))
(define (placeholder-extract! v fill!)
  (define loop placeholder-extract!)
  (match v
    [(or (== undefined) (? number?) (? boolean?) (? null?))
     (fill! v)]
    [(? vector?)
     (for ([i (in-naturals)]
           [e (in-vector v)])
       (loop e (λ (x) (vector-set! v i x))))
     (fill! v)]
    [(box bv)
     (loop bv (λ (x) (set-box! v x)))
     (fill! v)]
    [(mcons a d)
     (loop a (λ (x) (set-mcar! v x)))
     (loop d (λ (x) (set-mcdr! v x)))
     (fill! v)]
    [(? placeholder?)
     (cond
       [(placeholder-extracted? v)
        (fill! (placeholder-value v))]
       [else
        (define first-time? (null? (placeholder-fillers v)))
        (set-placeholder-fillers! v (cons fill! (placeholder-fillers v)))
        (when first-time?
          (loop (placeholder-value v)
                (λ (x)
                  (for ([fill! (in-list (placeholder-fillers v))])
                    (fill! x))
                  (set-placeholder-extracted?! v #t))))])]
    [(app (λ (x) (call-with-values (λ () (struct-info x)) list))
          (list (? struct-type? st) #f))
     (define-values
       (name
        init-field-cnt auto-field-cnt
        accessor-proc mutator-proc
        immutable-k-list super-type skipped?)
       (struct-type-info st))
     (for ([i (in-range init-field-cnt)])
       (loop (accessor-proc v i)
             (λ (x)
               (mutator-proc v i x))))
     (fill! v)]))

(define-syntax-rule (sharish ([x xe] ...) xb)
  (let ([x (empty-placeholder)] ...)
    (begin
      (placeholder-fill! x xe) ...
      (placeholder-extract! x (λ (xv) (set! x xv))) ...
      xb)))

(module+ test
  (require rackunit/chk)

  (struct posn (x y) #:mutable #:transparent)
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
