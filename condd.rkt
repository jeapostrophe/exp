#lang racket/base
(require (for-syntax racket/base
                     syntax/parse))
(module+ test
  (require rackunit/chk))

(define-syntax (condd stx)
  (syntax-parse stx
    #:literals (define else)
    [(_)
     #'(error 'condd "Missing else case")]
    [(_ [else . d])
     #'(let () . d)]
    [(_ (define . d) ...+ . more)
     #'(let ()
         (define . d) ...
         (condd . more))]
    [(_ [test . b] . more)
     #'(if test
         (let () . b)
         (condd . more))]))

(module+ test
  (chk
   (condd
    [else (void)])
   (void)

   (condd
    [else 1])
   1

   (condd
    (define first 1)
    [else (void)])
   (void)

   (condd
    [#t 1])
   1

   (condd
    (define first 1)
    [(= first 2)
     "2\n"]
    (define first 2)
    [(= first 2)
     "2 again\n"]
    [else
     "Nope\n"])
   "2 again\n"

   #:exn
   (condd
    [#f 1]
    [#f 2])
   "Missing else"))

(begin-for-syntax
  (define-splicing-syntax-class switch-clause
    #:attributes (code-gen)
    (pattern (~seq #:cond [t:expr e:expr ...+])
             #:attr code-gen
             (λ (k)
               (quasisyntax/loc #'t
                 (if t (let () e ...) #,k))))))

(define-syntax (switch stx)
  (syntax-parse stx
    [(_)
     (quasisyntax/loc stx
       (error 'switch "Fell through without else clause"))]
    [(_ #:else e:expr ...+)
     (syntax/loc stx
       (begin e ...))]
    [(_ (~and x (~not y:keyword)) ...
        sc:switch-clause . tail)
     (quasisyntax/loc stx
       (let ()
         x ...
         #,((attribute sc.code-gen)
            (syntax/loc stx
              (switch . tail)))))]))

(module+ test
  (chk #:exn (switch)
       "Fell through"

       (switch #:else 1)
       1

       (switch #:else 1 2)
       2

       (switch #:cond [1 2])
       2

       (switch #:cond [#f 1] #:else 2)
       2

       (switch #:cond [1 (define x 2) x])
       2

       (switch #:cond [#f 1] #:cond [2 3] #:else 4)
       3

       (switch (define one 1)
               #:cond [#f 1]
               (define two 2)
               #:cond [two (+ one one one)]
               #:else 4)
       3

       (switch (define-syntax-rule (one) 1)
               #:cond [#f 1]
               (define two 2)
               (set! two 3)
               #:cond [two (+ (one) two)]
               #:else 4)
       4))
