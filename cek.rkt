#lang racket/base
(require racket/match)

(struct pv () #:transparent)
(struct add pv () #:transparent)
(struct num pv (n) #:transparent)
(struct clo pv (term env) #:transparent)

(define step
  (match-lambda
   [(vector (? pv? pv) E `(* ,Ep ,e --> ,k))
    (vector e Ep `(,pv * --> ,k))]
   [(vector (? pv? pv) E 
            `(,(clo `(λ (,x) ,e) Ep) * --> ,k))
    (vector e (hash-set Ep x pv) k)]
   [(vector (? symbol? x) E k)
    (vector (hash-ref E x) E k)]
   [(vector `(,e ,ep) E k)
    (vector e E `(* ,E ,ep --> ,k))]
   [(vector `(λ (,x) ,e) E k)
    (vector (clo `(λ (,x) ,e) E) E k)]))

(define step*
  (match-lambda
   [(vector (? pv? pv) _ 'halt)
    pv]
   [st
    (step* (step st))]))

(define (eval e)
  (step* (vector e (hasheq) 'halt)))

(eval `(λ (s) (λ (z) z)))
(eval `(λ (s) (λ (z) (s z))))
(eval `(λ (n) (λ (m)
                (λ (s) (λ (z)
                         ((n s) ((m s) z)))))))
(eval `(((λ (n) (λ (m)
                  (λ (s) (λ (z)
                           ((n s) ((m s) z))))))
         (λ (s) (λ (z) (s z))))
        (λ (s) (λ (z) (s z)))))
