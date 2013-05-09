#lang racket

(define (term x)
  (if (zero? x)
    0
    (list 'app
          x
          (term (sub1 x))
          (term (sub1 x)))))

(struct painted (x c) #:transparent)

(define paintings-k 0)
(define (paint c t)
  (match t
    [(? list?)
     (set! paintings-k (add1 paintings-k))
     (map (λ (st) (paint c st)) t)]
    [(painted x (list oc ...))
     (define new
       (if (member c oc)
         (remove c oc)
         (cons c oc)))
     (if (empty? new)
       x
       (painted x new))]
    [x
     (painted x (list c))]))

(define (expand t)
  (define this-color (gensym 'color))
  (match (paint this-color t)
    [`(app ,n ,l ,r)
     (paint this-color 
            `(eapp ,n ,(expand l) ,(expand r)))]
    [n
     n]))

;; open : expanded-term -> name left right
(define (open t)
  (match t
    [`(eapp ,n ,l ,r)
     (vector n l r)]
    [n
     n]))

(define (open-all t)
  (match (open t)
    [(vector n l r)
     (vector n (open-all l) (open-all r))]
    [n
     n]))

(module+ main
  (define ex (term 3))
  'ex ex
  (define exe (expand ex))
  paintings-k
  'exe
  exe
  'opened
  (open-all exe))
