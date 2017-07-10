#lang racket/base
(require racket/list
         racket/match
         racket/pretty)

(define (snoc l x) (append l (list x)))
(define (search it initial-os)
  (define t->p (make-hash))
  (for ([os (in-list (permutations initial-os))])
    (define-values (fp ft)
      (for/fold ([p '()] [t it]) ([o (in-list os)])
        (match-define (cons n f) o)
        (values (cons n p) (f t))))
    (hash-set! t->p ft (reverse fp)))
  t->p)

;; Fighting Boys
#;(module+ main
  (pretty-print
   (search (list 'W)
           (list (cons 1 (λ (s) (reverse s)))
                 (cons 2 (λ (s) (cons 'N s)))
                 (cons 3 (λ (s) (list* 'G '_ s)))
                 (cons 4 (λ (s) (cons 'E (snoc s 'U))))
                 (cons 5 (λ (s) (cons 'N s)))))))

;; The Enchament
(module+ main
  (pretty-print
   (search '(T N)
           (list (cons 1 (λ (s) (append s '(E E))))
                 (cons 2 (λ (s) (append s '(T E E))))
                 (cons 3 (λ (s) (append '(S I) s '(N))))
                 (cons 4 (λ (s) (append '(X) s)))
                 (cons 5 (λ (s) (append '(X T) s)))
                 (cons 6 reverse))))) 
