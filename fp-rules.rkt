#lang racket

;; fp rules
(define fprops (make-weak-hash))
(define (fprop-set stx k v)
  (hash-update! fprops stx
                (λ (ht) (hash-set! ht k v))
                (λ () (make-hasheq)))
  stx)

(define (fexpand stx)
  (define my-+
    (match-lambda
     [`(+ ,lhs ,rhs)
      (cond
       [(zero? (fprop-get lhs 'num))
        rhs]
       [(zero? (fprop-get rhs 'num))
        lhs]
       [else
        (fprop-set `(+ ,lhs ,rhs)
                   'num
                   (safe+ (fprop-get lhs 'num)
                          (fprop-get rhs 'num)))])]))
  (define my-datum
    (match-lambda
     [(? number? n)
      (fprop-set n
                 'num
                 n)]))
  stx)

;; tests
(require tests/eli-tester)

(test
 (fexpand `(+ 0 1)) => `1
 (fexpand `(+ 1 0)) => `1
 (fexpand `(+ 1 3)) => `4
 (fexpand `(+ 1 x)) => `(+ 1 x)
 (fexpand `(+ 1 (+ -1 1))) => `1)
