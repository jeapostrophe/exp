#lang scheme/base
(require scheme/match)

(define-struct lst () #:prefab)
(define-struct (lst* lst) (v) #:prefab)
(define-struct (lst*-off lst) (head offset) #:prefab)
(define-struct (app lst) (l r) #:prefab)
(define-struct (cns lst) (car cdr) #:prefab)

(define (list* . xs)
  (make-lst* (list->vector xs)))
(define (append x y)
  (make-app x y))
(define (cons x y)
  (make-cns x y))

(define (car l)
  (list-ref* l 0))
(define (list-ref l i)
  (with-handlers ([exn:fail?
                   (lambda (x)
                     (error 'list-ref "index ~a too large for list: ~e"
                            i (->std l)))])
    (list-ref* l i)))

(define (list-ref* l i)
  (match l
    [(struct lst* (v))
     (define l (vector-length v))
     (if (i . < . (sub1 l))
         (vector-ref v i)
         (list-ref* (vector-ref v (sub1 l))
                    (- i (sub1 l))))]
    [(struct lst*-off (head offset))
     (list-ref* head (+ i offset))]
    [(struct app (l r))
     (define ll (length l))
     (if (i . < . ll)
         (list-ref* l i)
         (list-ref* r (- i ll)))]
    [(struct cns (a d))
     (if (zero? i)
         a
         (list-ref* d (sub1 i)))]
    [null
     (error 'car "expects argument of type <pair>; given ()")]))

(define (cdr l)
  (list-tail* l 1))
(define (list-tail l i)
  (with-handlers ([exn:fail?
                   (lambda (x)
                     (error 'list-tail "index ~a too large for list: ~e"
                            i (->std l)))])
    (list-tail* l i)))
(define (list-tail* L i)
  (if (zero? i)
      L
      (match L
        [(struct lst* (v))
         ; v = #(1 2 3 lst)
         (define l (vector-length v))
         ; l = 4
         (cond
           [(i . >= . l) ; i = 4, 5, 6
            (list-tail* (vector-ref v (sub1 l)) ; = lst
                        (- i (sub1 l)) ; = 0, 1, 2, 3
                        )]
           [else
            (make-lst*-off L i)])]
        [(struct lst*-off (head offset))
         (list-tail* head (+ i offset))]
        [(struct app (l r))
         (define ll (length l))
         (if (i . <= . ll)
             (append (list-tail* l i) r)
             (list-tail* r (- i ll)))]
        [(struct cns (a d))
         (if (= 1 i)
             d
             (list-tail* d (sub1 i)))]
        [null
         (error 'cdr "expects argument of type <pair>; given ()")])))

(define length
  (match-lambda
    [(struct lst* (v))
     (define l (vector-length v))
     (+ l -1 (length (vector-ref v (sub1 l))))]
    [(struct lst*-off (head offset))
     (- (length head) offset)]
    [(struct app (l r))
     (+ (length l) (length r))]
    [(struct cns (a d))
     (add1 (length d))]
    [null
     0]))

(define ->std
  (match-lambda
    [(struct lst* (v))
     (define l (vector-length v))
     (apply std:list* (std:append (vector->list (vector-take v (sub1 l)))
                                  (list (->std (vector-ref v (sub1 l))))))]
    [(struct lst*-off (head offset))
     (std:list-tail (->std head) offset)]
    [(struct app (l r))
     (std:append (->std l) (->std r))]
    [(struct cns (a d))
     (std:cons a (->std d))]
    [null
     null]))

; Tests
(require scheme/vector
         (prefix-in std: 
                    scheme/list)
         (prefix-in std:
                    scheme/base))
(define (random-lst i)
  (if (zero? i)
      'null
      (case (random 4)
        [(0) 'null]
        [(1) `(cons ,(random) ,(random-lst (sub1 i)))]
        [(2) `(list* ,(random) ,(random) ,(random) ,(random-lst (sub1 i)))]
        [(3) `(append ,(random-lst (sub1 i))
                      ,(random-lst (sub1 i)))])))
(define (lst-test l i)
  (case (random 5)
    [(0) `(car ,l)]
    [(1) `(cdr ,l)]
    [(2) `(list-ref ,l ,(random i))]
    [(3) `(list-tail ,l ,(random i))]
    [(4) `(length ,l)]))
(define (mk-test i)
  (lst-test (random-lst i) (* 2 i)))

(define relist
  (match-lambda
    [`null
     null]
    [`(cons ,i ,l)
     (cons i (relist l))]
    [`(list* ,i1 ,i2 ,i3 ,l)
     (list* i1 i2 i3 (relist l))]
    [`(append ,l1 ,l2)
     (append (relist l1) (relist l2))]))
(define run-test
  (match-lambda
    [`(car ,l)
     (car (relist l))]
    [`(cdr ,l)
     (cdr (relist l))]
    [`(list-ref ,l ,i)
     (list-ref (relist l) i)]
    [`(list-tail ,l ,i)
     (list-tail (relist l) i)]
    [`(length ,l)
     (length (relist l))]))

(define std:relist
  (match-lambda
    [`null
     null]
    [`(cons ,i ,l)
     (std:cons i (std:relist l))]
    [`(list* ,i1 ,i2 ,i3 ,l)
     (std:list* i1 i2 i3 (std:relist l))]
    [`(append ,l1 ,l2)
     (std:append (std:relist l1) (std:relist l2))]))
(define std:run-test
  (match-lambda
    [`(car ,l)
     (std:car (std:relist l))]
    [`(cdr ,l)
     (std:cdr (std:relist l))]
    [`(list-ref ,l ,i)
     (std:list-ref (std:relist l) i)]
    [`(list-tail ,l ,i)
     (std:list-tail (std:relist l) i)]
    [`(length ,l)
     (std:length (std:relist l))]))

(define-syntax-rule (wrap-error e)
  (with-handlers ([exn?
                   (lambda (x)
                     (regexp-replace #rx"for list:.*"
                                     (regexp-replace #rx"given:.*" (exn-message x) "")
                                     ""))])
    e))

(require tests/eli-tester)
(for ([j (in-range 1000)])
  (define t (mk-test 100))
  (define m (wrap-error (->std (run-test t))))
  (define s (wrap-error (std:run-test t)))
  (unless (equal? m s)
    (error 'test "Program ~S returned~n ~e~n rather than~n ~e"
           t m s)))