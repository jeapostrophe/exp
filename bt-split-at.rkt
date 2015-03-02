#lang racket/base
(require racket/match)
(module+ test
  (require rackunit))

(struct leaf () #:transparent)
(struct branch (left val right) #:transparent)

(define (insert t v)
  (match t
    [(leaf)
     (branch t v t)]
    [(branch l u r)
     (cond 
      [(< v u)
       (branch (insert l v) u r)]
      [(= v u)
       t]
      [else
       (branch l u (insert r v))])]))

(module+ test
  (define N 100)
  (define ex
    (foldr (λ (e a) (insert a e)) (leaf)
           (build-list N (λ (i) (random N))))))

(define (split-at t v)
  (match t
    [(leaf)
     (values t t)]
    [(branch l u r)
     (cond 
      [(< v u)
       (define-values (l< l>=) (split-at l v))
       (values l<
               (branch l>= u r))]
      [else
       (define-values (r< r>=) (split-at r v))
       (values (branch l u r<)
               r>=)])]))

(module+ test
  (define point (random N))
  (define-values (ex< ex>=)
    (split-at ex point))
  
  (require racket/pretty)
  (pretty-print point)
  (pretty-print ex<)
  (pretty-print ex>=))
