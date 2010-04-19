#lang scheme
(require mzlib/math
         (for-syntax syntax/parse))

(define (sec x)
  (/ 1 (cos x)))

(define (csc x)
  (/ 1 (sin x)))

(define (cot x)
  (/ 1 (tan x)))

(define (asec x)
  (acos (/ 1 x)))

(define (acsc x)
  (asin (/ 1 x)))

(define (acot x)
  (if (> x 0)
      (atan (/ 1 x))
      (+ (atan (/ 1 x) pi))))

(define-syntax (derivative stx)
  (syntax-parse
   stx
   #:literals (lambda + - * / expt log exp sin cos tan cot sec csc asin acos atan acot asec acsc)
   [(derivative (lambda formals b))
    (syntax/loc stx
      (lambda formals (derivative b)))]
   [(derivative (+ u ...))
    (syntax/loc stx
      (+ (derivative u) ...))]
   [(derivative (- u ...))
    (syntax/loc stx
      (- (derivative u) ...))]
   [(derivative (* u))
    (syntax/loc stx
      (derivative u))]
   [(derivative (* u v)) 
    (syntax/loc stx
      (+ (* u (derivative v)) (* v (derivative u))))]
   [(derivative (* u v ...))
    (syntax/loc stx
      (derivative (* u (* v ...))))]
   
   [(derivative (/ u))
    (syntax/loc stx
      (derivative u))]
   [(derivative (/ u v)) 
    (syntax/loc stx
      (/ (- (* v (derivative u)) (* u (derivative v)))
         (expt v 2)))]
   [(derivative (/ u v ...))
    (syntax/loc stx
      (derivative (/ u (/ v ...))))]
   
   [(derivative (expt u n)) 
    (syntax/loc stx
      (* (* n (expt u (- n 1))) (derivative u)))]
   [(derivative (log u)) 
    (syntax/loc stx
      (/ (derivative u) u))]
   [(derivative (exp u)) 
    (syntax/loc stx
      (* (exp u) (derivative u)))]
   [(derivative (sin u)) 
    (syntax/loc stx
      (* (cos u) (derivative u)))]
   [(derivative (cos u)) 
    (syntax/loc stx
      (* (- (sin u)) (derivative u)))]
   [(derivative (tan u)) 
    (syntax/loc stx
      (* (expt (sec u) 2) (derivative u)))]
   [(derivative (cot u)) 
    (syntax/loc stx
      (* (expt (csc u) 2) (derivative u)))]
   [(derivative (sec u)) 
    (syntax/loc stx
      (* (* (sec u) (tan u)) (derivative u)))]
   [(derivative (csc u)) 
    (syntax/loc stx
      (* (* (csc u) (cot u)) (derivative u)))]
   [(derivative (asin u)) 
    (syntax/loc stx
      (/ (derivative u) (sqrt (- 1 (expt u 2)))))]
   [(derivative (acos u)) 
    (syntax/loc stx
      (/ (- (derivative u)) (sqrt (- 1 (expt u 2)))))]
   [(derivative (atan u))
    (syntax/loc stx
      (/ (derivative u) (+ 1 (expt u 2))))]
   [(derivative (acot u)) 
    (syntax/loc stx
      (/ (- (derivative u)) (+ 1 (expt u 2))))]
   [(derivative (asec u))
    (syntax/loc stx
      (/ (derivative u) (* u (sqrt (- (expt u 2) 1)))))]
   [(derivative (acsc u))
    (syntax/loc stx
      (/ (- (derivative u)) (* (abs u) (sqrt (- (expt u 2) 1)))))]
   [(derivative x:id)
    (syntax/loc stx
      1)]
   [(derivative x:number)
    (syntax/loc stx
      0)]))

(derivative
 (lambda (x y z)
   (+ (* (cos x)
         (tan y)
         x)
      z
      (* 3 x)
      (/ x y))))
