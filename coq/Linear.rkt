#lang racket
(require rackunit)

(struct proof () #:transparent)
(struct proof:assume proof (p) #:transparent)
(struct proof:implies proof (a->p a) #:transparent)
(struct proof:weaken proof (more p) #:transparent)

(define prop-atoms
  (match-lambda
   [(? symbol? a)
    (list a)]
   [(list '-> lhs rhs)
    (append (prop-atoms lhs) (prop-atoms rhs))]))

(define proof-atoms
  (match-lambda
   [(proof:assume p)
    (prop-atoms p)]
   [(proof:implies lhs rhs)
    (append (proof-atoms lhs) (proof-atoms rhs))]
   [(proof:weaken ps p)
    (append (append-map prop-atoms ps) (proof-atoms p))]))

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

(define (unverified-proves env p)
  (let/cc return
    (prove env p
           (λ (proof new-env fk)
             (return
              (if (empty? new-env)
                proof
                (proof:weaken new-env proof))))
           (λ ()
             (return #f)))))

(require racket/runtime-path
         racket/pretty
         unstable/pretty)
(define-runtime-path coq-dir ".")
(define (verified-proves env the-prop)
  (match (unverified-proves env the-prop)
    [#f #f]
    [p

     (define v-pth (build-path coq-dir "LinearProof.v"))
     (define glob-pth (build-path coq-dir "LinearProof.glob"))
     (with-output-to-file v-pth
       #:exists 'replace
       (λ ()
         (printf "Require Import \"Linear\".\n")
         (printf "\n")

         ;; Atoms are hypotheses
         (for ([a (in-list (remove-duplicates (proof-atoms p)))])
           (printf "Hypothesis ~a : atom.\n"
                   a))
         (printf "\n")

         ;; Render each proof term
         (define proof-gamma
           (match-lambda
            [(proof:assume p)
             (list 'gamma_single
                   (print-prop p))]
            [(proof:weaken more p)
             (list 'gamma_union
                   (print-prop-list more)
                   (proof-gamma p))]
            [(proof:implies lhs rhs)
             (list 'gamma_union
                   (proof-gamma lhs)
                   (proof-gamma rhs))]))
         (define proof-prop
           (match-lambda
            [(proof:assume p)
             p]
            [(proof:weaken more p)
             (proof-prop p)]
            [(proof:implies a->p a)
             (third (proof-prop a->p))]))
         (define print-prop
           (match-lambda
            [(? symbol? a)
             (list 'Atom a)]
            [(list '-> lhs rhs)
             (list 'Implies
                   (print-prop lhs)
                   (print-prop rhs))]))
         (define print-prop-list
           (match-lambda
            [(list)
             'nil]
            [(cons car cdr)
             (list (print-prop car) ':: (print-prop-list cdr))]))
         (define print-proof
           (match-lambda
            [(proof:assume p)
             (list 'P_Assume (print-prop p))]
            [(proof:implies a->p a)
             (list 'P_Implies_Elim
                   (proof-gamma a->p)
                   (proof-gamma a)
                   (print-prop (proof-prop a))
                   (print-prop (third (proof-prop a->p)))
                   (print-proof a->p)
                   (print-proof a))]
            [(proof:weaken more p)
             (list 'P_Weak
                   (print-prop-list more)
                   (proof-gamma p)
                   (print-prop (proof-prop p))
                   (print-proof p))]))

         (define (prove-permutation structure l)
           (define (coq-append lhs rhs)
             (match lhs
               ['nil rhs]
               [`(,hd :: ,tl)
                `(,hd :: ,(coq-append tl rhs))]))
           (define (coq-remove x l)
             (match l
               ['nil
                (error 'coq-remove "~e not in list" x)]
               [`(,(== x) :: ,tl)
                tl]
               [`(,y :: ,tl)
                `(,y :: ,(coq-remove x tl))]))
           (define (coq-split-at-elem x l)
             (match l
               ['nil
                (error 'coq-split-at-elem "~e not in list" x)]
               [`(,(== x) :: ,tl)
                (values 'nil tl)]
               [`(,y :: ,tl)
                (define-values (before after) (coq-split-at-elem x tl))
                (values `(,y :: ,before) after)]))
           (define structure->coq-list
             (match-lambda
              ['nil 'nil]
              [`(,hd :: ,tl)
               `(,hd :: ,(structure->coq-list tl))]
              [`(gamma_union ,lhs ,rhs)
               (coq-append (structure->coq-list lhs)
                           (structure->coq-list rhs))]
              [`(gamma_single ,p)
               `(,p :: nil)]))
           (define in (print-prop-list l))
           (define out (structure->coq-list structure))

           (define inner
             (match-lambda*
              [(list 'nil 'nil)
               `(perm_nil prop)]
              [(list (list x ':: left)
                     (list x ':: right))
               `(perm_skip ,x ,(inner left right))]
              [(list (list y ':: left)
                     (list x ':: right))
               (define-values (before-y after-y)
                 (coq-split-at-elem y right))
               `(@Permutation_cons_app
                 prop
                 ,left
                 (,x :: ,before-y)
                 ,after-y
                 ,y
                 ,(inner left (list x ':: (coq-remove y right))))]))

           (inner out in))

         (printf "Check\n")
         (pretty-display
          (list (list 'P_Exchange
                      (proof-gamma p)
                      (print-prop-list env)
                      (print-prop (proof-prop p))
                      (prove-permutation (proof-gamma p) env)
                      (print-proof p))
                ':
                (list 'Proves
                      (print-prop-list env)
                      (print-prop the-prop))))
         (printf ".\n")))

     (define okay?
       (system* (find-executable-path "coqc")
                "-opt"
                v-pth))

     #;(delete-file v-pth)
     #;(delete-file glob-pth)

     (if okay?
       p
       (error 'verified-proves "Coq failed to check proof."))]))

(define proves verified-proves)

(check-equal?
 (proves '(a) 'a)
 (proof:assume 'a))

(check-equal?
 (proves '(b a) 'a)
 (proof:weaken '(b)
               (proof:assume 'a)))

(check-equal?
 (proves '(a b) 'a)
 (proof:weaken '(b)
               (proof:assume 'a)))

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
 (proves '(a c (-> a (-> c b)) d) 'b)
 (proof:weaken '(d)
               (proof:implies (proof:implies (proof:assume '(-> a (-> c b)))
                                             (proof:assume 'a))
                              (proof:assume 'c))))

(check-equal?
 (proves '((-> a a)) 'a)
 #f)

(proves '((-> part112 radio) part112 (-> radio car)) 'car)
