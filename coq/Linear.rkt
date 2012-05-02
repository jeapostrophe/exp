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

(define (subgoals-to-p a p)
  (match a
    [(== p)
     empty]
    [(list '-> lhs rhs)
     (define inner (subgoals-to-p rhs p))
     (and inner
          (list* lhs inner))]
    [_
     #f]))

(check-equal?
 (subgoals-to-p 'a 'a)
 '())
(check-equal?
 (subgoals-to-p '(-> b a) 'a)
 '(b))
(check-equal?
 (subgoals-to-p '(-> c (-> b a)) 'a)
 '(c b))

(define (prove env p sk fk)
  (every-split
   env sk fk
   (λ (hd tl sk fk)
     (match (subgoals-to-p hd p)
       [(list)
        (sk (proof:assume p) tl fk)]
       [(? list? subgoals)
        (define x (last subgoals))
        (prove (list* hd tl) (list '-> x p)
               (λ (proof-of-x->p new-tl x->p-fk)
                 (prove new-tl x
                        (λ (proof-of-x final-tl x-fk)
                          (sk (proof:implies proof-of-x->p
                                             proof-of-x)
                              final-tl
                              x-fk))
                        x->p-fk))
               fk)]
       [#f
        (fk)]))))

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

(check-equal?
 (proves '((-> a a)) 'a)
 #f)
