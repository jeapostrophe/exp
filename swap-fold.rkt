#lang racket/base
(require racket/list
         racket/function)

(define (foldr f a l)
  (cond
    [(empty? l)
     a]
    [else
     (f (first l) (foldr f a (rest l)))]))

(define (foldl f a l)
  (cond
    [(empty? l)
     a]
    [else
     (foldl f (f (first l) a) (rest l))]))

(define ((swap-folds base-fold) f a l)
  ((base-fold (λ (first-e k)
                (λ (next-e)
                  (k (f first-e next-e))))
              identity
              l)
   a))

(define foldr-foldl (swap-folds foldl))
(define foldl-foldr (swap-folds foldr))

(module+ test
  (require rackunit)

  (check-equal? (foldr string-append "[acc]" '("1" "2" "3"))
                "123[acc]")
  (check-equal? (foldl string-append "[acc]" '("1" "2" "3"))
                "321[acc]")
  (check-equal? (foldr-foldl string-append "[acc]" '("1" "2" "3"))
                "123[acc]")
  (check-equal? (foldl-foldr string-append "[acc]" '("1" "2" "3"))
                "321[acc]"))
