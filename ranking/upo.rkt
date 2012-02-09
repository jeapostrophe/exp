#lang racket
(require rackunit)

;; Sort by an partial order that is incompletely specified.

(define (implies p q)
  (or (not p) q))

(define (check-if-partial-order universe <=)
  (for ([a (in-list universe)])
       (test-true (format "Reflexivity of ~a" a)
                  (<= a a))
       (for ([b (in-list universe)])
            (test-true (format "Anti-Symmetry of ~a & ~a" a b)
                       (implies (and (<= a b) (<= b a))
                                (equal? a b)))
            (for ([c (in-list universe)])
                 (test-true (format "Transitivity of ~a & ~a & ~a" a b c)
                            (implies (and (<= a b) (<= b c))
                                     (<= a c)))))))

(check-if-partial-order '(1 2 3 4 5) <=)

(check-if-partial-order '(a) (λ (x y) #f))
