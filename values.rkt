#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     syntax/stx
                     racket/list
                     unstable/syntax)
         racket/list
         racket/match
         racket/package)

;; Uses the convention that a values+ has four parts: a code and the
;; arguments to keyword-apply
(define-package values+-pkg (call-with-values+ values+)
  (define value+-code
    (gensym))

  (define (call-with-values+ producer consumer)
    (call-with-values producer
      (case-lambda
        [(maybe-key kws kw-args rest)
         (if (eq? value+-code maybe-key)
           (keyword-apply consumer kws kw-args rest)
           (consumer maybe-key kws kw-args rest))]
        [args
         (apply consumer args)])))

  (define values+
    (make-keyword-procedure
     (lambda (kws kw-args . rest)
       (values value+-code kws kw-args rest))
     values)))

(open-package values+-pkg)

;; These macros are obvious
(define-syntax-rule (let-values+/one ([formals expr]) body)
  (call-with-values+ (lambda () expr) (lambda formals body)))

(define-syntax (let*-values+ stx)
  (syntax-case stx ()
    [(_ ([formals expr]) body)
     (syntax/loc stx
       (let-values+/one ([formals expr]) body))]
    [(_ ([formals0 expr0] [formals1 expr1] ...) body)
     (syntax/loc stx
       (let-values+/one ([formals0 expr0])
                        (let*-values+ ([formals1 expr1] ...) body)))]))

;; let-values+ is harder because we need to make sure the same things
;; are visible This function creates new names with the same structure
;; so let*-values+ can be used.
(define-for-syntax (generate-temporaries-for-formals stx)
  (syntax-parse
      stx
    [()
     (values #'()
             empty
             empty)]
    [rest:id
     (with-syntax ([(tmp-rest) (generate-temporaries #'(rest))])
       (values #'tmp-rest
               (list #'rest)
               (list #'tmp-rest)))]
    [(arg:id . more)
     (let-values ([(more-tmp-stx more-ids more-tmp-ids)
                   (generate-temporaries-for-formals #'more)])
       (with-syntax ([more-tmp more-tmp-stx]
                     [(tmp-arg) (generate-temporaries #'(arg))])
         (values #'(tmp-arg . more-tmp)
                 (list* #'arg more-ids)
                 (list* #'tmp-arg more-tmp-ids))))]
    [(kw:keyword . more)
     (let-values ([(more-tmp-stx more-ids more-tmp-ids)
                   (generate-temporaries-for-formals #'more)])
       (with-syntax ([more-tmp more-tmp-stx])
         (values #'(kw . more-tmp)
                 more-ids more-tmp-ids)))]
    [([arg:id default:expr] . more)
     (let-values ([(more-tmp-stx more-ids more-tmp-ids)
                   (generate-temporaries-for-formals #'(arg . more))])
       (with-syntax ([(tmp-arg . more-tmp) more-tmp-stx])
         (values #'([tmp-arg default] . more-tmp)
                 more-ids more-tmp-ids)))]))

(begin-for-syntax
  (define (generate-temporaries-for-formals/list stx)
    (define-values (tmp-stx stx-ids stx-tmp-ids)
      (generate-temporaries-for-formals stx))
    (list tmp-stx stx-ids stx-tmp-ids)))

(define-syntax (let-values+ stx)
  (syntax-case stx ()
    [(_ ([formals expr] ...) body)
     (with-syntax ([((temp-formals (formal-id ...) (temp-formal-id ...))
                     ...)
                    (stx-map generate-temporaries-for-formals/list
                             #'(formals ...))])
       (syntax/loc stx
         (let*-values+ ([temp-formals expr] ...)
                       (let-values ([(formal-id ...) (values temp-formal-id ...)]
                                    ...)
                         body))))]))

;; Tests
(module+ test
  (require tests/eli-tester)

  (test
   (call-with-values+ (lambda () (values 1))
                      (lambda (x) x))
   =>
   1

   (call-with-values+ (lambda () (values 2))
                      (lambda (x [y 3]) (list x y)))
   =>
   (list 2 3)

   (call-with-values+ (lambda () 3)
                      (lambda (x) x))
   =>
   3

   (call-with-values+ (lambda () 4)
                      (lambda (x [y 3]) (list x y)))
   =>
   (list 4 3)

   (call-with-values+ (lambda () (values+ 5 #:foo 3))
                      (lambda (x #:foo y) (list x y)))
   =>
   (list 5 3)

   (call-with-values+ (lambda () 6)
                      (lambda (x #:foo [y 3]) (list x y)))
   =>
   (list 6 3)

   (call-with-values+ (lambda () 7)
                      (lambda x x))
   =>
   (list 7)

   (let-values+ ([(x) 8]
                 [(y) 2])
                (list x y))
   =>
   (list 8 2)

   (let ([x 2])
     (let-values+ ([(x) 9]
                   [(y) x])
                  (list x y)))
   =>
   (list 9 2)

   (let-values+ ([x 10]
                 [(y) 2])
                (list x y))
   =>
   (list (list 10) 2)

   (let-values+ ([(x . xs) (values 10 10.2 10.3)]
                 [(y) 2])
                (list x xs y))
   =>
   (list 10 (list 10.2 10.3) 2)

   (let-values+ ([(x [z 3]) 11]
                 [(y) 2])
                (list x y z))
   =>
   (list 11 2 3)

   (let-values+ ([(x #:foo z) (values+ 12 #:foo 3)]
                 [(y) 2])
                (list x y z))
   =>
   (list 12 2 3)

   (let-values+ ([(x #:foo [z 3]) 13]
                 [(y) 2])
                (list x y z))
   =>
   (list 13 2 3)))

;; performance
(module+ main
  (define-syntax-rule
    (stress f [label code fun-body] ...)
    (stress*
     (list (cons 'label
                 (λ ()
                   (let ([f (λ () fun-body)])
                     code)))
           ...)))

  (define N (expt 10 6))
  (define (stress* fs)
    (define ts
      (for/list ([l*f (in-list fs)])
        (match-define (cons l f) l*f)
        (for ([i (in-range 3)])
          (collect-garbage))
        (define-values (a ct rt gt)
          (time-apply
           (λ ()
             (for ([i (in-range N)])
               (f)))
           empty))
        (cons l ct)))
    (define sts
      (sort ts < #:key cdr))
    (for ([l*t (in-list sts)])
      (match-define (cons l t) l*t)
      (printf "~a - ~a - ~a\n"
              (real->decimal-string
               (/ t (cdr (first sts))))
              l
              (real->decimal-string
               t))))

  (stress
   f
   [normal
    (let ([x (f)])
      (list x))
    1]

   [values1
    (let-values ([(x) (f)])
      (list x))
    (values 1)]
   [values2
    (let-values ([(x y) (f)])
      (list x y))
    (values 1 2)]
   [values3
    (let-values ([(x y z) (f)])
      (list x y z))
    (values 1 2 3)]
   [values4
    (let-values ([(x y z a) (f)])
      (list x y z a))
    (values 1 2 3 4)]
   [values5
    (let-values ([(x y z a b) (f)])
      (list x y z a b))
    (values 1 2 3 4 5)]
   [values6
    (let-values ([(x y z a b c) (f)])
      (list x y z a b c))
    (values 1 2 3 4 5 6)]
   [values7
    (let-values ([(x y z a b c d) (f)])
      (list x y z a b c d))
    (values 1 2 3 4 5 6 7)]

   [values+1
    (let-values+ ([(x) (f)])
                 (list x))
    (values+ 1)]
   [values+2
    (let-values+ ([(x y) (f)])
                 (list x y))
    (values+ 1 2)]
   [values+3
    (let-values+ ([(x y z) (f)])
                 (list x y z))
    (values+ 1 2 3)]
   [values+4
    (let-values+ ([(x y z a) (f)])
                 (list x y z a))
    (values+ 1 2 3 4)]
   [values+5
    (let-values+ ([(x y z a b) (f)])
                 (list x y z a b))
    (values+ 1 2 3 4 5)]
   [values+6
    (let-values+ ([(x y z a b c) (f)])
                 (list x y z a b c))
    (values+ 1 2 3 4 5 6)]
   [values+7
    (let-values+ ([(x y z a b c d) (f)])
                 (list x y z a b c d))
    (values+ 1 2 3 4 5 6 7)]

   [values+7kw
    (let-values+ ([(x y z a b c #:d d) (f)])
                 (list x y z a b c d))
    (values+ 1 2 3 4 5 6 #:d 7)]
   [values+7opt
    (let-values+ ([(x y z a b c [d 7]) (f)])
                 (list x y z a b c d))
    (values+ 1 2 3 4 5 6)]
   [values7opt
    (let-values+ ([(x y z a b c [d 7]) (f)])
                 (list x y z a b c d))
    (values 1 2 3 4 5 6)]
   [values+7kwopt
    (let-values+ ([(x y z a b c #:d [d 7]) (f)])
                 (list x y z a b c d))
    (values+ 1 2 3 4 5 6)]
   [values7kwopt
    (let-values+ ([(x y z a b c #:d [d 7]) (f)])
                 (list x y z a b c d))
    (values 1 2 3 4 5 6)]
   [values+7rest
    (let-values+ ([(x . xs) (f)])
                 (cons x xs))
    (values+ 1 2 3 4 5 6 7)]
   [values7rest
    (let-values+ ([(x . xs) (f)])
                 (cons x xs))
    (values 1 2 3 4 5 6 7)]))

;; XXX contracts
