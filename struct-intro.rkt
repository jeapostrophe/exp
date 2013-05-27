#lang racket/base
(require racket/list)

(struct posn (x y) #:transparent)
(struct 3posn posn (z) #:transparent #:mutable)

(define (dynamic-duplicate s)
  (define-values (s-type skipped?) (struct-info s))
  (when (or (not s-type) skipped?)
    (error 'dynamic-duplicate
           "Can't duplicate... structure not open"))

  (define ctor (struct-type-make-constructor s-type))

  (apply ctor
         (reverse
          (let loop ([t s-type] [skipped? skipped?])
            (cond
              [(and t (not skipped?))
               (define-values (name this-count _auto
                                    this-ref mutator immutable-idxs
                                    super super-skipped?)
                 (struct-type-info t))
               (append (for/list ([i (in-range 0 this-count)])
                         (this-ref s (- (sub1 this-count) i)))
                       (loop super super-skipped?))]
              [(and (not t) (not skipped?))
               empty]
              [else
               (error 'dynamic-duplicate
                      "Can't duplicate... parent structure not open")])))))

(module+ test
  (require rackunit)
  (define p1 (3posn 1 2 3))
  (define p2 (dynamic-duplicate p1))

  (set-3posn-z! p1 4)

  (check-equal? (posn-x p1) 1)
  (check-equal? (posn-y p1) 2)
  (check-equal? (3posn-z p1) 4)

  (check-equal? (posn-x p2) 1)
  (check-equal? (posn-y p2) 2)
  (check-equal? (3posn-z p2) 3))
