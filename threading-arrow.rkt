#lang racket/base
(require racket/stxparam
         (for-syntax racket/base
                     racket/list
                     syntax/parse))

;; Response to: http://www.greghendershott.com/2013/05/the-threading-macro.html

(begin-for-syntax
  (struct exn:fail:syntax:<> exn:fail:syntax ()))

(define-syntax-parameter <>s empty)

(define-syntax (<> stx)
  (syntax-parse stx
    [_:id
     (syntax/loc stx
       (<> 0))]
    [(_ idx:nat)
     (define l (syntax-parameter-value #'<>s))
     (define idx-v (syntax->datum #'idx))
     (if (> (length l) idx-v)
       (list-ref l idx-v)
       (if (empty? l)
         (raise (exn:fail:syntax:<> "<>: Only allowed inside ~>:"
                                    (current-continuation-marks)
                                    (list stx)))
         (raise-syntax-error '<> (format "~e is too large" idx-v) stx)))]))

(begin-for-syntax
  (define (contains-<>? stx)
    (with-handlers ([exn:fail:syntax:<>? (λ (x) #t)]
                    [(λ (x) #t) (λ (x) #f)])
      (local-expand #`(syntax-parameterize ([<>s empty]) #,stx)
                    'expression empty)
      #f)))

(define-syntax (ensure-<> stx)
  (syntax-parse stx
    [(_ e:expr)
     (if (contains-<>? #'e)
       (syntax/loc stx e)
       (syntax/loc stx (e <>)))]))

(define-syntax (~> stx)
  (syntax-parse stx
    [(_ last:expr)
     (syntax/loc stx
       last)]
    [(_ rand:expr rator:expr more:expr ...)
     (syntax/loc stx
       (let ([rand-v rand])
         (syntax-parameterize
             ([<>s (list* #'rand-v (syntax-parameter-value #'<>s))])
           (~> (ensure-<> rator) more ...))))]))

(module+ test
  (require rackunit
           racket/function)

  (define-syntax-rule (check-equal2? a b c)
    (begin (check-equal? a b)
           (check-equal? b c)))

  (check-equal2?
   (~> (list 1 2 3)
       (map add1 <>)
       (curry map add1)
       (λ (xs) (map add1 xs))
       (sort <> >)
       list->vector)

   (list->vector
    (sort ((λ (xs) (map add1 xs))
           ((curry map add1)
            (map add1 (list 1 2 3))))
          >))

   (vector 6 5 4))

  (check-equal2?
   (~> (~> (list 1 2 3)
           (map add1 <>))
       (~> <>)
       list->vector)

   (list->vector
    (map add1 (list 1 2 3)))

   (vector 2 3 4))

  (check-equal2?
   (~> (~> (list 1 2 3)
           (map add1 <>))
       (~> <>
           (curry map add1))
       list->vector)

   (list->vector
    ((curry map add1)
     (map add1 (list 1 2 3))))

   (vector 3 4 5))

  (check-equal2?
   (~> (~> (list 1 2 3)
           (map add1 <>))
       (~> <>
           (map add1 <>))
       list->vector)

   (list->vector
    (map add1
         (map add1 (list 1 2 3))))

   (vector 3 4 5))

  (check-equal?
   (~> 1
       (+ <>)
       (+ <> (<> 1))
       (+ <> (<> 1) (<> 2)))
   (let* ([s0 1]
          [s1 (+ s0)]
          [s2 (+ s1 s0)]
          [s3 (+ s2 s1 s0)])
     s3))

  (check-equal2?
   (~> (~> (list 1 2 3)
           (map add1 <>))
       (~> <>
           (map add1 <>)
           (map + (<> 2) <>))
       list->vector)

   (list->vector
    (let ([s2 (map add1 (list 1 2 3))])
      (let ([s1 (map add1 s2)])
        (map + s2 s1))))

   (vector 5 7 9)))
