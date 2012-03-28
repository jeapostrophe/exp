#lang racket/base

(struct clo (term env))

(define step
  (match-lambda
   [(vector (? clo? pv) E `(* ,Ep ,e --> ,k))
    (vector e Ep `(,pv * ,k))]
   [(vector (? clo? pv) E `(,(clo `(λ (,x) ,e) ,Ep) * --> ,k))
    (vector e (hash-set Ep x pv) k)]
   [(vector (? symbol? x) E k)
    (vector (hash-ref E x) E k)]
   [(vector `(,e ,ep) E k)
    (vector e E `(* ,E ,ep --> ,k))]
   [(vector `(λ (,x) ,e) ,E ,k)
    (vector (clo `(λ (,x) ,e) E) E k)]))

(define step*
  (match-lambda
   [(vector (clo t _) _ 'halt)
    t]
   [st
    (step* (step st))]))

(define (eval e)
  (step* (vector e (hasheq) 'halt)))
