#lang racket

(define-syntax
  (define-ast stx)
  (syntax-case stx ()
    [(_
      [(parent its-parent) (child field ...)
       ...])
     (syntax/loc stx
       (begin
         (struct parent its-parent ()
                 #:transparent)
         (struct child parent (field ...)
                 #:transparent)
         ...))]
    [(_
      [parent (child field ...)
              ...])
     (syntax/loc stx
       (begin
         (struct parent ()
                 #:transparent)
         (struct child parent (field ...)
                 #:transparent)
         ...))]))
(define-syntax-rule (define-asts class ...)
  (begin (define-ast class) ...))

(define-asts
  [t
   (app rator rand)
   (tyapp t T)]
  [(v t)
   (num n)
   (succ)
   (abs T x->t)
   (tyabs T->t)]
  [T
   (Nat)
   (arr dom rng)
   (tyall X->T)])

(define double
  (tyabs
   (λ (X)
     (abs (arr X X)
          (λ (f)
            (abs X
                 (λ (a)
                   (app f (app f a)))))))))

(define (ex1 arg)
  (app
   (app (tyapp double (Nat))
        (abs (Nat)
             (λ (x)
               (app (succ)
                    (app (succ)
                         x)))))
   arg))

(define eval
  (match-lambda
   ;; E-StopAtValues
   [(? v? v) v]
   ;; E-App1
   [(app (and (not (? v?)) t1) t2)
    (eval (app (eval t1) t2))]
   ;; E-App2
   [(app (? v? v1) (and (not (? v?)) t2))
    (eval (app v1 (eval t2)))]
   ;; E-AppAbs
   [(app (abs T_11 x->t_12) (? v? v_2))
    (eval (x->t_12 v_2))]
   ;; E-Succ
   [(app (succ) (num n))
    (num (add1 n))]
   ;; E-TApp
   [(tyapp (and (not (? v?)) t1) T_2)
    (eval (tyapp (eval t1) T_2))]
   ;; E-TAppTAbs
   [(tyapp (tyabs X->t_12) (? T? T_2))
    (eval (X->t_12 T_2))]))

(define tyinst
  (match-lambda
   [(Nat)
    (num 0)]
   [(arr dom rng)
    (abs dom (λ (x) (tyinst rng)))]
   [(tyall X->T)
    (tyabs (λ (X) (tyinst (X->T X))))]))

(define type-of
  (match-lambda
   ;; T-App
   [(app rator rand)
    (match (type-of rator)
      [(arr dom rng)
       (and (equal? dom (type-of rand))
            rng)]
      [_ #f])]
   ;; T-TApp
   [(tyapp t T)
    (match (type-of t)
      [(tyall X->T)
       (X->T T)]
      [_ #f])]
   ;; T-Num
   [(num n)
    (Nat)]
   ;; T-Succ
   [(succ)
    (arr (Nat) (Nat))]
   ;; T-Abs
   [(abs T x->T)
    (arr T
         (type-of (x->T (tyinst T))))]
   ;; T-TAbs
   [(tyabs T->t)
    (tyall (λ (X) (type-of (T->t X))))]))

(define (run t)
  (if (type-of t)
    (eval t)
    (error 'run "Does not type check")))

(require tests/eli-tester)
(test
 (run (tyapp (tyinst (tyall (λ (X) X)))
             (Nat)))
 => 
 (num 0)

 (run (app (tyapp (tyinst (tyall (λ (X) X)))
                  (arr (Nat) (Nat)))
           (num 1)))
 =>
 (num 0)

 (run (ex1 (num 3))) 
 => 
 (num 7)

 (run (ex1 (abs (Nat) (λ (x) x))))
 =>
 (error 'run "Does not type check"))
