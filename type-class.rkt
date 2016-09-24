#lang racket/base
(require racket/match)

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

(define-class (MonadPlus m)
  #:constraint (Monad m)
  mzero
  mplus)

(define-instance () (MonadPlus option)
  (define mzero (none))
  (define (mplus x y)
    (match* (x y)
      [((none)   (none))   x]
      [((some _) (none))   x]
      [((none)   (some _)) y]
      [(_        _)        x])))

(define-generic (a) #:constraint (MonadPlus a)
  (msum l)
  (foldr mplus mzero l))

(define-class (Functor a)
  fmap)

(define-instance (a) (Functor a)
  #:constraint (Monad a)
  (define (fmap ab ma) (>>= ma (λ (x) (return (ab x))))))

(with-instances [(Monad option) (MonadPlus option) (Functor option)]
  (fmap add1 (msum (list (none) (return 5) (none)))))
