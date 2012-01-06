#lang racket/base

;;;;;;; By hand using my regime
(require racket/match
         racket/list)

;; lang =
(struct lang ())

;; e := 
(struct e lang ())
;;      | (e e ...)
(struct e:app e (es))
;;      | v

;; v :=
(struct v e ())
;;      (vlist v ...)
(struct v:vlist v (vs))
;;      list
(struct v:list v ())
;;      car
(struct v:car v ())
;;      cdr
(struct v:cdr v ())
;;      +
(struct v:+ v ())
;;      num
(struct v:num v (n))

(define (not-v? x) 
  (not (v? x)))

;; E :=
(struct E lang ())
;;      | (v ... E e ...)
(struct E:app E (vs E es))
;;      | hole
(struct E:hole ())

(define inside:->
  (match-lambda
   [(e:app (list-rest (v:list) vs))
    (v:vlist vs)]
   [(e:app (list (v:car) (v:vlist vs)))
    (first vs)]
   [(e:app (list (v:car)  (v:vlist vs)))
    (v:vlist (rest vs))]
   [(e:app (list-rest (v:+) ns))
    (v:num (apply + (map v:num-n ns)))]
   [_ #f]))

(define decompose
  (match-lambda
   [(e:app (list (? v? vs) ... (? not-v? e_0) e_n ...))
    (define-values (E inside) (decompose e_0))
    (values (E:app vs E e_n)
            inside)]
   [e
    (values (E:hole)
            e)]))

(define (plug ctxt plugged)
  (match 
   ctxt
   [(E:app vs E es)
    (e:app (append vs (list* (plug E plugged) es)))]
   [(E:hole)
    plugged]))

(define (outside:-> e)
  (define-values (E redex) (decompose e))
  (define redactum (inside:-> redex))
  (and redactum
       (plug E redactum)))

(define (outside:->* e)
  (define e-p (outside:-> e))
  (if e-p
      (outside:->* e-p)
      e))

(define parse
  (match-lambda
   [(list 'vlist v ...)
    (v:vlist (map parse v))]
   [(? list? es)
    (e:app (map parse es))]
   [(? number? n)
    (v:num n)]
   ['list (v:list)]
   ['car (v:car)]
   ['cdr (v:cdr)]
   ['+ (v:+)]))

(define unparse
  (match-lambda
   [(e:app es)
    (map unparse es)]
   [(v:vlist vs)
    (list* 'vlist (map unparse vs))]
   [(v:num n)
    n]
   [(v:list) 'list]
   [(v:car) 'car]
   [(v:cdr) 'cdr]
   [(v:+) '+]))

(define (parse+->* t)
  (unparse (outside:->* (parse t))))

;;;;;;; Redex

(require (except-in redex/reduction-semantics
                    plug))

(define-language redex:lang
  [v (vlist v ...)
     list
     car
     cdr
     +
     number]
  [e (e e ...)
     v]
  [E (v ... E e ...)
     hole])

(define redex->
  (reduction-relation 
   redex:lang
   #:domain e
   [--> (in-hole E (list v ...))
        (in-hole E (vlist v ...))]
   [--> (in-hole E (+ v ...))
        (in-hole E ,(apply + (term (v ...))))]
   [--> (in-hole E (car (vlist v_0 v ...)))
        (in-holE E v_0)]
   [--> (in-hole E (cdr (vlist v_0 v ...)))
        (in-holE E (vlist v ...))]))

;; Compare

(define-syntax-rule (time-it e)
  (let* ([start-time (current-inexact-milliseconds)]
         [ans (with-handlers ([exn? (λ (x) 'error)])
                             e)]
         [end-time (current-inexact-milliseconds)])
    (values ans
            (- end-time start-time))))

(define (compare t)
  (define-values (redex:ans redex:time)
    (time-it (first (apply-reduction-relation* redex-> t))))
  (define-values (jay:ans jay:time) (time-it (parse+->* t)))
  (cond
   [(not (equal? redex:ans jay:ans))
    (error 'compare "Mismatch ~s vs ~s"
           redex:ans
           jay:ans)]
   [(jay:time . < . redex:time)
    (printf "Jay wins by ~a\n"
            (- redex:time jay:time))]
   [else
    (printf "Redex wins by ~a\n"
            (- jay:time redex:time))]))

(printf "Random terms\n")
(for ([i (in-range 10)])
     (compare (generate-term redex:lang e i)))

(printf "Exponential terms\n")

(define (generate-exponential i)
  (cond
   [(zero? i)
    1]
   [else
    (define next (generate-exponential (sub1 i)))
    (list '+
          next
          next)]))

(for ([i (in-range 10)])
     (compare (generate-exponential i)))
