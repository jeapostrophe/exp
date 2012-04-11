#lang racket
(require rackunit)

(define (test-table* table-t)
  (parameterize
      ([current-test-case-around
        (λ (row-t)
          (printf "~a\t" (current-test-name))
          (parameterize
              ([current-test-case-around
                (λ (col-t)
                  (with-handlers ([exn:test:check?
                                   (λ (x)
                                     (printf "~a\t" (string-upcase (current-test-name))))])
                    (col-t)
                    (printf "~a\t" (current-test-name))))])
            (row-t))
          (printf "\n"))])
    (table-t)))

(define-syntax-rule (test-table e ...)
  (test-table* (λ () e ...)))

;;;;;;;;;;

(define (something x)
  (test-equal? "zero" x 0)
  (define y (even? x))
  ;; save y to a file
  (test-equal? "even" y #t)
  (define z (odd? x))
  ;; save z to a file
  (test-equal? "odd" z #t))

(test-table
 (for ([i (in-range 10)])
   (test-case (number->string i)
              (something i))))
