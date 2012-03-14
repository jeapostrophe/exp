#lang racket

(define-syntax
  (define-stx-class stx)
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
(define-syntax-rule (define-stxs class ...)
  (begin (define-stx-class class) ...))

(define-stxs
  [v (num n)
     (succ)
     (abs T x->t)
     (tyabs T->t)]
  [(t v)
   (app rator rand)
   (tyapp t T)]
  [T (Nat)
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
   ;; E-App1
   [(app (and (not (? v?)) t1) t2)
    (eval (app (eval t1) t2))]
   ;; E-App2
   [(app (? v? v1) (and (not (? v?)) t2))
    (eval (app v1 (eval t2)))]
   [x
    (error 'eval "Cannot eval: ~v" x)]))

(define (type-of t)
  #t)

(define (run t)
  (if (type-of t)
    (eval t)
    (error 'run "Does not type check")))

(require tests/eli-tester)
(test
 (run (ex1 (num 3))) => (num 7)

 (run (ex1 (abs (Nat) (λ (x) x))))
 => 
 (error 'run "Does not type check"))

