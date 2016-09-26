#lang racket/base
(require racket/match)

;; XXX Add the default: x >> y = x >>= \_ . y
(define-class (Monad m)
  return
  >>=)

(struct option ())
(struct some option (a))
(struct none option ())
(define-instance () (Monad option)
  (define (return a) (just a))
  (define (>>= oa f)
    (match oa
      [(some a) (f a)]
      [(none) oa])))

;; A sub-class
(define-class (MonadPlus m)
  #:constraint (Monad m)
  mzero
  mplus)

;; You don't have to explicitly satisfy the constraints?
(define-instance () (MonadPlus option)
  (define mzero (none))
  (define (mplus x y)
    (match* (x y)
      [((none)   (none))   x]
      [((some _) (none))   x]
      [((none)   (some _)) y]
      [(_        _)        x])))

;; Function defined over any class instance
(define-generic (a) #:constraint (MonadPlus a)
  (msum l)
  (foldr mplus mzero l))

(define-class (Functor a)
  fmap)

;; Derived instance
(define-instance (a) (Functor a)
  #:constraint (Monad a)
  (define (fmap ab ma)
    (>>= ma (λ (x) (return (ab x))))))

;; XXX There needs to be another form for when one context needs two
;; different instances.
(with-instances [(Monad option) (MonadPlus option) (Functor option)]
  (fmap add1 (msum (list (none) (return 5) (none)))))

;; XXX https://wiki.haskell.org/Functional_dependencies
;; XXX https://wiki.haskell.org/Type_families
;; XXX https://wiki.haskell.org/Multi-parameter_type_class
