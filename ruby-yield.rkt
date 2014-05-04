#lang racket/base
(require racket/list
         racket/match
         racket/stxparam
         (for-syntax racket/base))

(define YIELD-STACK (box empty))

(define-syntax-parameter break (λ (stx) (raise-syntax-error 'break stx)))

(define (yield)
  (match-define (cons top more) (unbox YIELD-STACK))
  (set-box! YIELD-STACK more)
  (top))
(define-syntax-rule (call-with-block fun block)
  (let/ec this-break 
    (set-box! YIELD-STACK 
              (cons (syntax-parameterize
                        ([break (make-rename-transformer #'this-break)])
                      block)
                    (unbox YIELD-STACK)))
    fun))

(module+ test
  (define (foo x)
    (printf "E~a, " x)
    (if (x . >= . 5)
      (yield)
      (call-with-block
       (foo (x . + . 1))
       (λ ()
        (printf "B~a, " x)
        (if (x . <= . 2)
          (break)
          (yield)))))
    (printf "L~a, " x))
  (foo 1)
  (printf "END\n")

  (printf "\nshould be\n\n")

  (printf "E1, E2, E3, E4, E5, B4, B3, B2, L2, L1, END\n"))
