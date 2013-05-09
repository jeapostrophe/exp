#lang racket

(define (term x)
  (if (zero? x)
    0
    (list 'app
          x
          (term (sub1 x))
          (term (sub1 x)))))

(struct painted (x c) #:transparent)
(struct paint-promise (c t) #:transparent)

(define paintings-k 0)
(define (paint c t)
  (match t
    [(paint-promise (list oc ...) t)
     (define new
       (if (member c oc)
         (remove c oc)
         (cons c oc)))
     (if (empty? new)
       t
       (paint-promise new t))]
    [(? list?)
     (paint-promise (list c) t)]
    [(painted x (list oc ...))
     (define new
       (if (member c oc)
         (remove c oc)
         (cons c oc)))
     (if (empty? new)
       x
       (painted x new))]
    ['app
     'app]
    ['eapp
     'eapp]
    [(? number? x)
     (painted x (list c))]
    [x
     (error 'paint "~e" x)]))

(define (expand t)
  (define this-color (gensym 'color))
  (match (open (paint this-color t))
    [`(app ,n ,l ,r)
     (paint this-color 
            `(eapp ,n ,(expand l) ,(expand r)))]
    [(? number? n)
     n]
    [(painted x c)
     t]
    [x
     (error 'expand "~e" x)]))

;; open : expanded-term -> name left right
(define (open t)
  (match t
    [(paint-promise c t)
     (set! paintings-k (add1 paintings-k))
     (map (λ (st) (paint c st)) t)]
    [`(,_ ,n ,l ,r)
     (vector n l r)]
    [(? number? n)
     n]
    [(painted x c)
     t]
    [x
     (error 'open "~e" x)]))

(define (open-all t)
  (match (open t)
    [`(,_ ,n ,l ,r)
     (vector n (open-all l) (open-all r))]
    [(vector n l r)
     (vector n (open-all l) (open-all r))]
    [(? number? n)
     n]
    [(painted x c)
     t]
    [x
     (error 'open-all "~e" x)]))

(module+ main
  (define ex (term 3))
  'ex ex
  (define exe (expand ex))
  paintings-k
  'exe
  exe
  'opened
  (open-all exe))
