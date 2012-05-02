#lang racket
(require rackunit)

(struct proof () #:transparent)
(struct proof:assume proof (p) #:transparent)
(struct proof:implies proof (a->p a) #:transparent)

(define (every-split l sk fk f)
  (let/cc esc
    (for ([i (in-range (length l))])
      (define-values (before after) (split-at l i))
      (define hd (first after))
      (define tl (append before (rest after)))
      
      (let/cc next
        (f hd tl (λ (p e fk) (esc (sk p e fk))) next)))

    (fk)))

(define (prove env p sk fk)
  (every-split
   env
   sk fk
   (λ (hd tl sk fk)
     (match hd
       [(== p)
        (sk (proof:assume p) tl fk)]
       [(list '-> a (== p))
        (prove tl a
               (λ (proof-of-a new-tl fk)
                 (sk (proof:implies
                      (proof:assume hd)
                      proof-of-a)
                     new-tl
                     fk))
               fk)]
       ;; May have (a -> (b -> p))
       [_
        (fk)]
       ))))

(define (proves env p)
  (let/cc return
    (prove env p
           (λ (proof new-env fk)
             (return proof))
           (λ () 
             (return #f)))))

(check-equal?
 (proves '(a) 'a)
 (proof:assume 'a))

(check-equal?
 (proves '(b a) 'a)
 (proof:assume 'a))

(check-equal?
 (proves '(a b) 'a)
 (proof:assume 'a))

(check-equal?
 (proves '(b) 'a)
 #f)

(check-equal?
 (proves '((-> a b) a) 'b)
 (proof:implies (proof:assume '(-> a b))
                (proof:assume 'a)))

(check-equal?
 (proves '(a (-> a b)) 'b)
 (proof:implies (proof:assume '(-> a b))
                (proof:assume 'a)))

(check-equal?
 (proves '(a (-> a c) (-> c b)) 'b)
 (proof:implies (proof:assume '(-> c b))
                (proof:implies (proof:assume '(-> a c))
                               (proof:assume 'a))))

(check-equal?
 (proves '(a c (-> a (-> c b))) 'b)
 (proof:implies (proof:implies (proof:assume '(-> a (-> c b)))
                               (proof:assume 'a))
                (proof:assume 'c)))
