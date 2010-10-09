#lang racket
(require racket/stxparam)
(define-syntax-parameter break
  (λ (stx) (raise-syntax-error 'break "Used outside cas-cad-e" stx)))
(define-syntax-rule (cas-cad-e e [(n ...) code ...] ...)
  (let/ec esc
    (syntax-parameterize 
     ([break (make-rename-transformer #'esc)])
     (let*-values 
         ([(tmp) e]
          [(earlier? ret) (values #f (void))]
          [(earlier? ret) 
           (if (or earlier? (equal? tmp n) ...)
               (values #t (begin code ...))
               (values earlier? ret))]
          ...)
       ret))))

(require tests/eli-tester)

(define printed "")
(define (cas1 v)
  (set! printed "")
  (cas-cad-e v
             [(1) (set! printed (string-append printed "1"))]
             [(2) (set! printed (string-append printed "2")) (break 2)]
             [(3) 3]))

(test (cas1 1) => 2
      printed => "12"
      (cas1 2) => 2
      printed => "2"
      (cas1 3) => 3
      printed => ""
      (cas1 4) => (void)
      printed => "")

(define (cas3 v)
  (let ([w true])
    (cas-cad-e v
               [(0) (set! w false)]
               [(1) (if w (break 1) (break 0))])))

(test (cas3 0) => 0
      (cas3 1) => 1)