#lang racket

(define K 11)

;;

(require redex)

(define-language lang
  [e number
     (+ e e)])

(define ex1
  (term-match 
   lang
   [(+ e 0)
    (term e)]))

(define huge-term1
  (local [(define (make-term n)
            (if (zero? n)
                1
                (let ([m (make-term (sub1 n))])
                  (term (+ ,m ,m)))))]
    (make-term K)))

(collect-garbage) (collect-garbage)
(time
 (void (ex1 (term (+ ,huge-term1 0)))))

;;

(define-struct lang:e:num (n))
(define-struct lang:e:+ (e1 e2))

(define ex2
  (match-lambda
    [(lang:e:+ e (lang:e:num 0))
     e]
    [_
     #f]))

(define huge-term2
  (local [(define (make-term n)
            (if (zero? n)
                (make-lang:e:num 1)
                (make-lang:e:+ (make-term (sub1 n)) (make-term (sub1 n)))))]
    (make-term K)))

(collect-garbage) (collect-garbage)
(time
 (void (ex2 (make-lang:e:+ huge-term2 (make-lang:e:num 0)))))