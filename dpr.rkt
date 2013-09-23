#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/stxparam)

(define-syntax-parameter queue-defer #f)
(define-syntax (defere stx)
  (define qdv (syntax-parameter-value #'queue-defer))
  (unless qdv
    (raise-syntax-error 'defer "Illegal use outside of define/dpr" stx))
  (syntax-parse stx
    [(_ (f a ...))
     (with-syntax ([(v ...) (generate-temporaries #'(a ...))])
       (quasisyntax/loc stx
         (#,qdv (let ([v a] ...) (λ () (f v ...))))))]))

(define-syntax-parameter return
  (λ (stx) (raise-syntax-error 'return "Illegal use outside of define/dpr" stx)))

(struct exn:fail:panic exn:fail (v [recovered? #:mutable]))
(define (panic v)
  (raise (exn:fail:panic (format "panic ~e" v) (current-continuation-marks) v #f)))

(define current-panic (make-parameter #f))
(define (recover)
  (define p (current-panic))
  (and p
       (set-exn:fail:panic-recovered?! p #t)
       (exn:fail:panic-v p)))

(define-syntax (define/dpr-v1 stx)
  (syntax-parse stx
    [(_ (fun . fmls) . body)
     (syntax/loc stx
       (define (fun . fmls)
         (define ds null)
         (define (this-queue-defer f)
           (set! ds (cons f ds)))
         (define (run-defers)
           (for ([d (in-list ds)])
             (d)))
         (begin0
           (with-handlers ([exn:fail:panic?
                            (λ (p)
                              (parameterize ([current-panic p])
                                (run-defers))
                              (unless (exn:fail:panic-recovered? p)
                                (raise p)))])
             (let/ec this-return
               (syntax-parameterize ([queue-defer #'this-queue-defer]
                                     [return (make-rename-transformer #'this-return)])
                 . body))
             (run-defers)))))]))

(define-syntax (define/dpr stx)
  (syntax-parse stx
    [(_ (fun . fmls) . body)
     (syntax/loc stx
       (define (fun . fmls)
         (define ds null)
         (define (this-queue-defer f)
           (set! ds (cons (box f) ds)))
         (define (run-defers)
           (for ([db (in-list ds)])
             (define d (unbox db))
             (set-box! db #f)
             (when d
               (d))))
         (begin0
           (with-handlers ([exn:fail:panic?
                            (λ (p)
                              (parameterize ([current-panic p])
                                (run-defers))
                              (unless (exn:fail:panic-recovered? p)
                                (raise p)))])
             (let/ec this-return
               (syntax-parameterize ([queue-defer #'this-queue-defer]
                                     [return (make-rename-transformer #'this-return)])
                 . body))
             (run-defers)))))]))

(define-syntax-rule (defer . e)
  (defere ((λ () . e))))

(module+ test
  (require rackunit)

  (define-syntax-rule (test c e o)
    (begin
      (define os (open-output-string))
      (check-equal? (parameterize ([current-output-port os])
                      (with-handlers ([exn:fail:panic?
                                       (λ (p)
                                         (exn:fail:panic-v p))])
                        c))
                    e)
      (check-equal? (get-output-string os) o)))

  (define/dpr (a)
    (define i 0)
    (defere (printf "~a\n" i))
    (set! i (add1 i))
    (return (void)))

  (test (a) (void) "0\n")

  (define/dpr (b)
    (for ([i (in-range 4)])
      (defer (printf "~a" i))))

  (test (b) (void) "3210")

  ;; xxx Named function returns would be a lot more complicated, so we
  ;; don't have example c

  (define/dpr (main recover?)
    (f recover?)
    (printf "Returned normally from f.\n"))

  (define/dpr (f recover?)
    (when recover?
      (defer
        (define r (recover))
        (when r
          (printf "Recovered in f ~a\n" r))))
    (printf "Calling g.\n")
    (g 0)
    (printf "Returned normally from g.\n"))

  (define/dpr (g i)
    (when (> i 3)
      (printf "Panicking!\n")
      (panic (format "~a" i)))
    (defer (printf "Defer in g ~a\n" i))
    (printf "Printing in g ~a\n" i)
    (g (add1 i)))

  (test (main #t) (void) "Calling g.\nPrinting in g 0\nPrinting in g 1\nPrinting in g 2\nPrinting in g 3\nPanicking!\nDefer in g 3\nDefer in g 2\nDefer in g 1\nDefer in g 0\nRecovered in f 4\nReturned normally from f.\n")
  (test (main #f) "4" "Calling g.\nPrinting in g 0\nPrinting in g 1\nPrinting in g 2\nPrinting in g 3\nPanicking!\nDefer in g 3\nDefer in g 2\nDefer in g 1\nDefer in g 0\n")

  (define/dpr (panic-in-defer)
    (defer (displayln 0))
    (defer (displayln 1))
    (defer
      (displayln 2)
      (panic '!))
    (defer (displayln 3)))

  (test (panic-in-defer) '! "3\n2\n1\n0\n"))
