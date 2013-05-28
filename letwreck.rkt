#lang racket/base
(require (except-in rackunit fail)
         racket/list)

(define f #f)
(define-syntax-rule (function=? a b)
  (begin (set! f a)
         (equal? (quote a) (quote b))))

(check-false
 (function=? (λ (x) (+ x 1))
             (λ (x) (add1 x))))

(check-equal? (f 1) 2)

(define q (quote (λ (x) (+ x 1))))
(check-true (list? q))
(check-equal? (first q) 'λ)
(check-equal? (second q) '(x))
(check-equal? (third q) '(+ x 1))

(define g (λ (y) (+ y 4)))

(define-syntax-rule (m e)
  (if (list? 'e)
    e
    (error 'm "I own you")))

(check-equal? (m ((λ (x) (+ 1 x)) 5)) 6)
(check-exn exn:fail? (λ () (m 6)))

(define-syntax sexp=?
  (syntax-rules ()
    ((sexp=? (a1 . b1) (a2 . b2) yes no)
     (sexp=? a1 a2 (sexp=? b1 b2 yes no) no))
    ((sexp=? (a1 . b1) e2 yes no)
     no)
    ((sexp=? e1 (a2 . b2) yes no)
     no)
    ((sexp=? #(e1 ...) #(e2 ...) yes no)
     (sexp=? (e1 ...) (e2 ...) yes no))
    ((sexp=? #(e1 ...) e2 yes no)
     no)
    ((sexp=? e1 #(e2 ...) yes no)
     no)
    ((sexp=? e1 e2 yes no)
     (ident? e1
             (ident? e2 (ident=? e1 e2 yes no) no)
             (ident? e2 no (const=? e1 e2 yes no))))))

(define-syntax ident?
  (syntax-rules ()
    ((ident? a yes no)
     (let-syntax ((test (syntax-rules ()
                          ((test a y n) y)
                          ((test _ y n) n))))
       (test *anident* yes no)))))

(check-true (ident? x #t #f))

(check-true (ident? y #t #f))

(check-true (let-syntax ((test (syntax-rules ()
                                 ((test x y n) y)
                                 ((test _ y n) n))))
              (test *anident* #t #f)))

(check-false (ident? 5 #t #f))

(check-false (let-syntax ((test (syntax-rules ()
                                  ((test 5 y n) y)
                                  ((test _ y n) n))))
               (test *anident* #t #f)))

(check-false (ident? (x y) #t #f))

(define-syntax ident=?
  (syntax-rules ()
    ((ident=? a b yes no)
     (let-syntax ((test (syntax-rules (a)
                          ((test a y n) y)
                          ((test x y n) n))))
       (test b yes no)))))

(define-syntax const=?
  (syntax-rules ()
    ((const=? a b yes no)
     (let-syntax ((test (syntax-rules ()
                          ((test a y n) y)
                          ((test _ y n) n))))
       (test b yes no)))))

(check-false
 (sexp=? (λ (x) (+ x 1))
         (λ (x) (add1 x))
         #t
         #f))
(check-true
 (sexp=? (λ (x) (+ x 1))
         (λ (x) (+ x 1))
         #t
         #f))

(check-false
 (sexp=? (λ (x) (+ x 1))
         (λ (x) (add1 x))
         unbound-identifier
         #f))

(define-syntax-rule (mylet ([y ye]) be)
  ((λ (y) be) ye))

(check-equal? (mylet ([x 5]) (+ x 5)) 10)

(define-syntax-rule (weird-macro1 (operator x operand))
  (let ([x 5]) (operator x operand)))

(check-equal? (weird-macro1 (+ x 5))
              10)

(define-syntax find
  (syntax-rules ()
    ((find ident (a . b) sk fk)
     (find ident a sk (find ident b sk fk)))
    ((find ident #(a ...) sk fk)
     (find ident (a ...) sk fk))
    ((find ident a (sk-op . sk-args) fk)
     (ident? a
             (ident=? ident a (sk-op a . sk-args) fk)
             fk))))

(define-syntax loop
  (syntax-rules ()
    ((loop e)
     (let-syntax ((k (syntax-rules ()
                       ((_ ident e*)
                        (call/cc (lambda (ident)
                                   (let f ()
                                     e*
                                     (f))))))))
       (find break e (k e) (k dummy e))))
    ((loop es ...)
     (loop (begin es ...)))))

(module+ test
  (let ()
    (define x 0)
    (define-syntax-rule (lambda (x) e)
      42)
    (loop (set! x (+ x 1))
          (display x)
          (when (>= x 100)
            (break #f)))))

;; a diversion on success & failure continuations

(define next-choice #f)
(define (pick opts)
  (cond
    [(empty? opts)
     (fail)]
    [else
     (let/cc the-rest-of-the-program
       (define last-choice next-choice)
       (set! next-choice
             (λ ()
               (set! next-choice last-choice)
               (the-rest-of-the-program
                (pick (rest opts)))))
       (the-rest-of-the-program (first opts)))]))
(define (fail)
  (if next-choice
    (next-choice)
    (error 'fail)))

(let ()
  (let* ([x (pick '(1 2 3 4 5 6 7 8 9))]
         [y (pick '(3 4 5 6 7 8 9))])
    (printf "Before X is ~a, Y is ~a\n" x y)
    (unless (= x (* 2 y))
      (fail))
    (printf "After X is ~a, Y is ~a\n" x y)))

(define (epick opts call-me-on-success call-me-on-failure)
  (cond
    [(empty? opts)
     (call-me-on-failure)]
    [else
     (call-me-on-success
      (first opts)
      (λ ()
        (epick (rest opts)
               call-me-on-success
               call-me-on-failure)))]))

(epick '(1 2 3 4 5 6 7 8 9)
       (λ (x xs-fail)
         (epick '(3 4 5 6 7 8 9)
                (λ (y ys-fail)
                  (printf "eBefore X is ~a, Y is ~a\n" x y)
                  (if (= x (* 2 y))
                    (printf "eAfter X is ~a, Y is ~a\n" x y)
                    (ys-fail)))
                (λ ()
                  (xs-fail))))
       (λ ()
         (error 'fail)))

;; alpha renaming

(let ()
  (define (f x)
    (+ x 1))
  (f 1))

(let ()
  (define (f y)
    (+ y 1))
  (f 1))

(let ()
  (define (f a-long-descriptive-name-for-this-variable)
    (+ a-long-descriptive-name-for-this-variable 1))
  (f 1))

(let ()
  (define (this-f a-long-descriptive-name-for-this-variable)
    (+ a-long-descriptive-name-for-this-variable 1))
  (this-f 1))

;; binding specifications

(define-syntax-rule
  ;;   this         is bound here
  ;;     |            |
  ;;     v            v
  (jlet ([x xe] ...) be)
  ((λ (x ...) be) xe ...))

(define-syntax jlet*
  (syntax-rules ()
    [(_ () be)
     be]
    [(_ ([x0     ;; <-- this
          xe0]
         ;;       is bound here
         ;; vvvvvvvvvvvvvvvvvvvv
         [xN xeN]
         ...) be)
     (jlet ([x0 xe0])
           (jlet* ([xN xeN] ...)
                  be))]))

(define-syntax jletrec
  (syntax-rules ()
    [(_ ([xN ;; <- these are bound everywhere inside the jletrec
          xeN] ...) be)
     (jlet ([xN #f]
            ...)
           (begin (set! xN xeN)
                  ...
                  be))]))

(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax))
(define-syntax (jletwreck stx)
  (syntax-parse stx
    [(_ ([binding:id (other-binding:id ...) bound-body:expr]
         ...)
        body:expr)
     (with-syntax* ([(new-binding ...)
                     (generate-temporaries #'(binding ...))]
                    [((new-other-binding ...) ...)
                     (for/list ([obs (in-list (syntax->list #'((other-binding ...) ...)))])
                       (for/list ([ob (in-list (syntax->list obs))])
                         (for/or ([old (in-list (syntax->list #'(binding ...)))]
                                  [new (in-list (syntax->list #'(new-binding ...)))])
                           (and (bound-identifier=? old ob)
                                new))))])
                   (syntax/loc stx
                     (jletrec ([new-binding
                                (let-syntax ([other-binding (make-rename-transformer #'new-other-binding)]
                                             ...)
                                  bound-body)] ...)
                              (let-syntax ([binding (make-rename-transformer #'new-binding)]
                                           ...)
                                body))))]))

(jlet ([x 'x] [y 'y] [z 'z] [h 'h] [i 'i])
      (jletwreck
       ([x (i) (list x y z h i)]
        [y (x) (list x y z h i)]
        [z (y) (list x y z h i)]
        [h (x z) (list x y z h i)]
        [i () (list x y z h i)])
       (list x y z h i)))

(define-syntax-rule (t e) (λ () e))
(define-syntax-rule (tlist e ...) (t (list (e) ...)))
(jlet ([x (t 'x)] [y (t 'y)] [z (t 'z)] [h (t 'h)] [i (t 'i)])
      (jletwreck
       ([x (i) (tlist x y z h i)]
        [y (x) (tlist x y z h i)]
        [z (y) (tlist x y z h i)]
        [h (x z) (tlist x y z h i)]
        [i () (tlist x y z h i)])
       ((tlist x y z h i))))
