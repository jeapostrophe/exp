#lang racket

; The code
(define (raw f)
  (f void))

(define (client seed use-affine)
  (random-seed seed)
  (use-affine
   (λ (f)
     (define used? #f)
     (for ([i (in-range 100)])
       (sync (alarm-evt (random 100)))
       (unless (or used? (zero? (random 3)))
         (set! used? #t)
         (f))))))

(define (bad-client use-affine)
  (use-affine
   (λ (f)
     (f) (f))))

; The benchmarks
(require "temporal.rkt")

(define ctc
  (contract
   (-> (-> (-> any) any/c) any/c)
   raw 'pos 'neg))

(define aff->
  (make-contract
   #:name 'affine
   #:first-order procedure?
   #:projection
   (λ (b)
     (λ (f)
       (define called? #f)
       (λ ()
         (when called?
           (raise-blame-error b f "called twice!"))
         (set! called? #t)
         (f))))))
(define ad-hoc
  (contract
   (-> (-> aff-> any/c) any/c)
   raw 'pos 'neg))

(require "regexp.rkt")
(define make-rgx-monitor
  (make-evt-regexp-predicate
   (evt:call 'affine proj _ _ _ _ _) _ ...
   (evt:call 'affine proj _ _ _ _ _) _ ...))
(define rgx
  (contract
   (-> (*->t make-rgx-monitor 'affine void))
   raw 'pos 'neg))

; The runner
(require tests/stress)
(define seed (+ 1 (random (expt 2 30))))
(define-syntax-rule (STRESS version ...)
  (begin
    (with-handlers ([exn:fail? (λ (x) (void))])
      (bad-client version)
      (printf "~a is bad\n" 'version))
    ...
    (newline)
    (stress 4 
            [(symbol->string 'version)
             (client seed version)]
            ...)))

(STRESS raw ctc ad-hoc)


