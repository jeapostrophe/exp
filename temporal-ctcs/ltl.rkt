#lang racket/base
(require racket/match
         racket/list)

; XXX Good contracts
(provide (all-defined-out))

(struct ltl () #:transparent)
(struct ltl:P ltl (?) #:transparent)
(struct ltl:not ltl (sub) #:transparent)
(struct ltl:and ltl (phi psi) #:transparent)
(define (ltl:or phi psi)
  (ltl:not (ltl:and (ltl:not phi) (ltl:not psi))))
(define (ltl:-> phi psi)
  (ltl:or (ltl:not phi) psi))
(define ltl:true
  (ltl:P (λ (e) #t)))
(define ltl:false
  (ltl:P (λ (e) #f)))
; U means "find something that matches psi and make sure everything before matches phi"
(struct ltl:U (phi psi) #:transparent)
(define (ltl:eventually f)
  (ltl:U ltl:true f))
(define (ltl:always f)
  (ltl:not (ltl:eventually (ltl:not f))))
(define (ltl:V phi psi)
  (ltl:not (ltl:U (ltl:not phi) (ltl:not psi))))
(struct ltl:X ltl (f) #:transparent)

(define (models w f)
  (match f
    [(ltl:P ?)
     (match w
       [(cons x_0 _)
        (? x_0)]
       [_
        #f])]
    [(ltl:X f)
     (match w
       [(cons _ x_1)
        (models x_1 f)]
       [_
        #f])]
    [(ltl:not f)
     (not (models w f))]
    [(ltl:and phi psi)
     (and (models w phi) (models w psi))]
    [(ltl:U phi psi)
     #;(for/or ([i (in-range 0 (length w))])
         (define w_i (list-tail w i))
         (and (models w_i psi)
              (for/and ([j (in-range 0 i)])
                (define w_j (list-tail w j))
                (models w_j phi))))
     ; This has lower complexity because we don't call list-tail,
     ; which iterates over the prefix on every round
     ; Ideally, we would have written (in-list-tails l)
     (let i-loop ([w_i w]
                  [i 0])
       (if (empty? w_i)
           #f
           (or
            (and (models w_i psi)
                 (let j-loop ([w_j w]
                              [j 0])
                   (if (= j i)
                       #t
                       (and (models w_j phi)
                            (j-loop (rest w_j) (add1 j))))))
            (i-loop (rest w_i) (add1 i)))))]))

(require rackunit
         racket/function)

(define-syntax-rule (test-ltl-false l f)
  (begin (check-false (models l f))))
(define-syntax-rule (test-ltl-true l f)
  (begin (check-true (models l f))))
  
(test-ltl-false empty ltl:true)
(test-ltl-false empty ltl:false)
(test-ltl-true (list 1) ltl:true)
(test-ltl-false (list 1) ltl:false)

(test-ltl-true (list 1) (ltl:P odd?))
(test-ltl-false (list 1) (ltl:P even?))

(test-ltl-false (list 1) (ltl:not (ltl:P odd?)))
(test-ltl-true (list 1) (ltl:not (ltl:P even?)))

(test-ltl-true (list 1) (ltl:and (ltl:P odd?) (ltl:P (curry = 1))))
(test-ltl-false (list 1) (ltl:and (ltl:P even?) (ltl:P (curry = 1))))
(test-ltl-false (list 1) (ltl:and (ltl:P odd?) (ltl:P (curry = 2))))
(test-ltl-false (list 1) (ltl:and (ltl:P even?) (ltl:P (curry = 2))))

(test-ltl-true (list 1) (ltl:or (ltl:P odd?) (ltl:P (curry = 1))))
(test-ltl-true (list 1) (ltl:or (ltl:P even?) (ltl:P (curry = 1))))
(test-ltl-true (list 1) (ltl:or (ltl:P odd?) (ltl:P (curry = 2))))
(test-ltl-false (list 1) (ltl:or (ltl:P even?) (ltl:P (curry = 2))))

(test-ltl-false (list 1) (ltl:-> (ltl:P odd?) (ltl:P (curry = 2))))
(test-ltl-true (list 1) (ltl:-> (ltl:P odd?) (ltl:P (curry = 1))))
(test-ltl-true (list 1) (ltl:-> (ltl:P even?) (ltl:P (curry = 2))))
(test-ltl-true (list 2) (ltl:-> (ltl:P even?) (ltl:P (curry = 2))))

(test-ltl-true (list 1 2) (ltl:U (ltl:P odd?) (ltl:P even?)))
(test-ltl-true (list 1 2 1) (ltl:U (ltl:P odd?) (ltl:P even?)))
(test-ltl-false (list 1) (ltl:U (ltl:P odd?) (ltl:P even?)))

(test-ltl-true (list 1) (ltl:eventually (ltl:P odd?)))
(test-ltl-false (list 2) (ltl:eventually (ltl:P odd?)))
(test-ltl-true (list 2 1) (ltl:eventually (ltl:P odd?)))
(test-ltl-true (list 1 2) (ltl:eventually (ltl:P odd?)))

(test-ltl-true (list 1) (ltl:always (ltl:P odd?)))

(test-ltl-false (list 1) (ltl:U ltl:true (ltl:not (ltl:P odd?))))
(test-ltl-true (list 1) (ltl:not (ltl:U ltl:true (ltl:not (ltl:P odd?)))))

(test-ltl-false (list 1 1) (ltl:U ltl:true (ltl:not (ltl:P odd?))))
(test-ltl-true (list 1 1) (ltl:not (ltl:U ltl:true (ltl:not (ltl:P odd?)))))
(test-ltl-true (list 1 1) (ltl:V ltl:false (ltl:P odd?)))
(test-ltl-true (list 1 1) (ltl:always (ltl:P odd?)))
(test-ltl-false (list 2) (ltl:always (ltl:P odd?)))
(test-ltl-false (list 2 1) (ltl:always (ltl:P odd?)))
(test-ltl-false (list 1 2) (ltl:always (ltl:P odd?)))

; XXX I don't have an intuition for V

(test-ltl-true (list 2 1) (ltl:X (ltl:P odd?)))
(test-ltl-false (list 1 2) (ltl:X (ltl:P odd?)))
(test-ltl-true (list 2) (ltl:not (ltl:X (ltl:P odd?))))

(define only-odd?-once (ltl:always (ltl:-> (ltl:P odd?) (ltl:X (ltl:always (ltl:not (ltl:P odd?)))))))
(test-ltl-true empty only-odd?-once)
(test-ltl-true (list 1) only-odd?-once)
(test-ltl-true (list 1 2) only-odd?-once)
(test-ltl-true (list 2 1 2) only-odd?-once)
(test-ltl-true (list 2 1 2 2) only-odd?-once)
(test-ltl-false (list 1 1) only-odd?-once)
(test-ltl-false (list 1 2 1) only-odd?-once)
(test-ltl-false (list 1 2 2 1) only-odd?-once)
(test-ltl-false (list 2 1 2 1 2) only-odd?-once)
