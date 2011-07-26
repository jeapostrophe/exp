#lang s-exp "../../core/racket-with-pkgs.rkt"
(require racket/unsafe/ops)

(define (every-other l)
  (if (null? l)
      null
      (cons (unsafe-car l)
            (every-other (unsafe-cdr (unsafe-cdr l))))))

(provide every-other)