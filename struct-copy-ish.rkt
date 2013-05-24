#lang racket/base
(require (for-syntax racket/base
                     racket/struct-info
                     racket/list
                     racket/syntax
                     racket/match
                     syntax/parse)
         racket/match)

(begin-for-syntax
  (define (snoc x l)
    (append l (list x)))
  (define (split-atf ? l)
    (let loop ([b empty] [l l])
      (cond
        [(or (empty? l) (? (first l)))
         (values (reverse b) l)]
        [else
         (loop (cons (first l) b)
               (rest l))]))))

(define-syntax (struct-update stx)
  (syntax-parse stx
    [(_ top (mid ...)
        e:expr
        [f:id fe:expr])
     #:declare top (static struct-info? "structure binding")
     #:declare mid (static struct-info? "structure binding")
     (with-syntax*
      ([top-f (format-id #'top "~a-~a" #'top #'f)]
       [((opt? opt (opt-before ...) (opt-after ...)) ...)
        (for/list ([s (in-list (snoc (attribute top.value)
                                     (attribute mid.value)))])
          (match-define (list _ constructor predicate
                              (list accessors-r ...)
                              _
                              _)
                        (extract-struct-info s))
          (define accessors (reverse accessors-r))
          (define-values (before it*after)
            (split-atf
             (λ (x) (free-identifier=? #'top-f x))
             accessors))
          (list predicate constructor
                before (rest it*after)))])
      (syntax/loc stx
        (let ([v e]
              [fv fe])
          (match v
            [(? opt?)
             (opt (opt-before v) ...
                  fv
                  (opt-after v) ...)]
            ...))
        ))]))

(define-syntax (struct-copy-ish stx)
  (syntax-parse stx
    [(_ top (mid ...) e)
     (syntax/loc stx e)]
    [(_ top (mid ...) e [f0 fe0] [f fe] ...)
     (syntax/loc stx
       (struct-copy-ish top (mid ...)
                        (struct-update top (mid ...) e [f0 fe0])
                        [f fe] ...))]))

;; example
(module+ test
  (require rackunit)

  (struct posn (x y))
  (struct 3posn posn (z))

  (define e1 (3posn 1 2 3))
  (define e2 (struct-copy-ish posn (3posn) e1 [x 5] [y 7]))
  
  (check-equal? (posn-x e2) 5)
  (check-equal? (posn-y e2) 7)
  (check-equal? (3posn-z e2) 3))
