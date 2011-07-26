#lang s-exp "../../core/racket-with-pkgs.rkt"
(require racket/list
         racket/contract)

(define (every-other l)
  (if (null? l)
      empty
      (cons (car l)
            (every-other (cdr (cdr l))))))

(define (even-length-list? l)
  (and (list? l)
       (even? (length l))))

(provide/contract
 [every-other (-> even-length-list? list?)]) 