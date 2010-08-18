#lang racket

(define K 10)

;;

(require redex/reduction-semantics)

(define-language lang
  [e number
     (+ e e)]
  [E hole
     (+ E e)
     (+ number E)])

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

(printf "Match:\n")
(time
 (void (ex1 (term (+ ,huge-term1 0)))))

(define +-red1
  (reduction-relation 
   lang
   #:domain e
   [--> (in-hole E (+ number_0 number_1))
        (in-hole E ,(+ (term number_0) (term number_1)))]))

(define (eval1 e)
  (define es (apply-reduction-relation +-red1 e))
  (if (empty? es)
      e
      (eval1 (first es))))

(printf "Eval:\n")
(time (eval1 huge-term1))

;;
(newline)
(collect-garbage) (collect-garbage)
;;

(define-struct lang:e:num (n))
(define-struct lang:e:+ (e1 e2))
(define-struct lang:E:hole ())
(define-struct lang:E:left (E1 e2))
(define-struct lang:E:right (num1 E1))

(define ex2
  (match-lambda
    [(lang:e:+ e (lang:e:num 0))
     e]
    [_
     #f]))

(define huge-term2
  (local [(define (make-term n)
            (if (zero? n)
                (lang:e:num 1)
                (lang:e:+ (make-term (sub1 n)) (make-term (sub1 n)))))]
    (make-term K)))

(printf "Match:\n")
(time
 (void (ex2 (lang:e:+ huge-term2 (make-lang:e:num 0)))))

(define-struct lang:in-hole (E1 e1))
(define decompose2
  (match-lambda
    [(? lang:e:num? e)
     (lang:in-hole (lang:E:hole) e)]
    [(and e (lang:e:+ (lang:e:num n1) (lang:e:num n2)))
     (lang:in-hole (lang:E:hole) e)]
    [(lang:e:+ (? lang:e:num? n1) e2)
     (match-define (lang:in-hole E e) (decompose2 e2))
     (lang:in-hole (lang:E:right n1 E) e)]
    [(lang:e:+ e1 e2)
     (match-define (lang:in-hole E e) (decompose2 e1))
     (lang:in-hole (lang:E:left E e2) e)]))

(define plug2
  (match-lambda
    [(lang:in-hole E e)
     (plug2i E e)]))
(define (plug2i E e)
  (match E
    [(lang:E:hole) e]
    [(lang:E:left E1 e2)
     (lang:e:+ (plug2i E1 e) e2)]
    [(lang:E:right num1 E2)
     (lang:e:+ num1 (plug2i E2 e))]))

(define (+-red2d e)
  (match (decompose2 e)
    [(lang:in-hole E (lang:e:+ (lang:e:num n1) (lang:e:num n2)))
     (list (plug2 (lang:in-hole E (lang:e:num (+ n1 n2)))))]
    [_
     empty]))

(define (eval2d e)
  (define es (+-red2d e))
  (if (empty? es)
      e
      (eval2d (first es))))

(printf "Eval (dumb):\n")
(time (lang:e:num-n (eval2d huge-term2)))

(define (decompose2s e ei)
  (match e
    [(? lang:e:num?)
     (lang:in-hole ei e)]
    [(and e (lang:e:+ (lang:e:num n1) (lang:e:num n2)))
     (lang:in-hole ei e)]
    [(lang:e:+ (? lang:e:num? n1) e2)
     (decompose2s e2 (lang:E:right n1 ei))]
    [(lang:e:+ e1 e2)
     (decompose2s e1 (lang:E:left ei e2))]))

(define redecompose2
  (match-lambda
    [(lang:in-hole (lang:E:right n1 nE) v2)
     (lang:in-hole nE (lang:e:+ n1 v2))]
    [(lang:in-hole (lang:E:left nE e2) v1)
     (decompose2s e2 (lang:E:right v1 nE))]
    [(and d (lang:in-hole (lang:E:hole) v1))
     d]))

(define +-red2s
  (match-lambda
    [(lang:in-hole E (lang:e:+ (lang:e:num n1) (lang:e:num n2)))
     (list (redecompose2 (lang:in-hole E (lang:e:num (+ n1 n2)))))]
    [_
     empty]))

(define (eval2s e)
  (lang:in-hole-e1 (eval2si (decompose2s e (lang:E:hole)))))
(define (eval2si d)
  (define es (+-red2s d))
  (if (empty? es)
      d
      (eval2si (first es))))

(printf "Eval (smart):\n")
(time (lang:e:num-n (eval2s huge-term2)))

