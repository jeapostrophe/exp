#lang racket/base
(require racket/match)

(struct tree ())
(struct tree:n0 tree ())
(struct tree:n1 tree (next))
(struct tree:n2 tree (left k v right))

(define (lookup t k d)
  (match t
    [(tree:n0)
     d]
    [(tree:n1 t)
     (lookup t k d)]
    [(tree:n2 l bk bv r)
     (cond
      [(<= k bk)
       (lookup l k d)]
      [else
       (lookup r k d)])]))

(define (insert t k v)
  (define ins
    (match-lambda
     [(tree:n0)
      (fake:l2 k v)]
     [(tree:n1 t)
      (fake:n1 (ins t))]
     [(tree:n2 l bk bv r)
      (cond
       [(<= k bk)
        (fake:n2 (ins l) bk bv r)]
       [else
        (fake:n2 l bk bv (ins r))])]))
  (root (ins t)))

(struct fake ())
(struct fake:l2 fake (k v))
(struct fake:n3 fake (left k1 v1 middle k2 v2 right))

(define root
  (match-lambda
   [(fake:l2 k v)
    (tree:n2 (tree:n0) k v (tree:n0))]
   [(fake:n3 t1 k1 v1 t2 k2 v2 t3)
    (tree:n2 (tree:n2 t1 k1 v1 t2) k2 v2 (tree:n1 t3))]
   [t
    t]))

(define fake:n1
  (match-lambda
   [(fake:l2 k v)
    (tree:n2 (tree:n0) k v (tree:n0))]
   [(fake:n3 t1 k1 v1 t2 k2 v2 t3)
    (tree:n2 (tree:n2 t1 k1 v1 t2) k2 v2 (tree:n1 t3))]
   [t
    (tree:n1 t)]))

(define fake:n2
  (match-lambda*
   [(list (fake:l2 k1 v1) k2 v2 t1)
    (fake:n3 (tree:n0) k1 v1 (tree:n0) k2 v2 t1)]
   [(list (fake:n3 t1 k1 v1 t2 k2 v2 t3) k3 v3 (tree:n1 t4))
    (tree:n2 (tree:n2 t1 k1 v1 t2) k2 v2 (tree:n2 t3 k3 v3 t4))]
   [(list (fake:n3 t1 k1 v1 t2 k2 v2 t3) k3 v3 (? tree:n2? t4))
    (fake:n3 (tree:n2 t1 k1 v1 t2) k2 v2 (tree:n1 t3) k3 v3 t4)]

   [(list t1 k1 v1 (fake:l2 k2 v2))
    (fake:n3 t1 k1 v1 (tree:n0) k2 v2 (tree:n0))]
   [(list (tree:n1 t1) k1 v1 (fake:n3 t2 k2 v2 t3 k3 v3 t4))
    (tree:n2 (tree:n2 t1 k1 v1 t2) k2 v2 (tree:n2 t3 k3 v3 t4))]
   [(list (? tree:n2? t1) k1 v1 (fake:n3 t2 k2 v2 t3 k3 v3 t4))
    (fake:n3 t1 k1 v1 (tree:n1 t2) k2 v2 (tree:n2 t3 k3 v3 t4))]

   [(list t1 k1 v1 t2)
    (tree:n2 t1 k1 v1 t2)]))

(module+ test
  (define (simple-insert t k v)
    (match t
      [(tree:n0) (tree:n2 t k v t)]
      [(tree:n2 l bk bv r)
       (cond
        [(<= k bk)
         (tree:n2 (simple-insert l k v) bk bv r)]
        [else
         (tree:n2 l bk bv (simple-insert r k v))])]))

  (require slideshow
           pict
           pict/tree-layout)

  (define (layout t)
    (match t
      [(tree:n0) (tree-layout)]
      [(tree:n1 t) (tree-layout (layout t))]
      [(tree:n2 l k v r)
       (tree-layout #:pict (text (format "~v = ~v" k v))
                    (layout l)
                    (layout r))]))

  (require racket/list)

  (define (from-list l insert inform!)
    (foldr (λ (k t)
             (define n (insert t k #t))
             (inform! n)
             n)
           (tree:n0)
           l))

  (for ([n (in-range 16)])
    (define base-l (for/list ([i (in-range (add1 n))]) i))
    (define l
      (match 0
        [0 base-l]
        [1 (shuffle base-l)]
        [2 (reverse base-l)]))
    (define (draw! t)
      (slide
       (naive-layered
        (layout t))))
    (slide
     (naive-layered
      (layout
       (from-list l insert void)))
     (naive-layered
      (layout
       (from-list l simple-insert void))))))
