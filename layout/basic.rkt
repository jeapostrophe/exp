#lang racket/base
(require (only-in '#%foreign ctype-basetype)
         racket/list
         racket/match
         ffi/unsafe)
(module+ test
  (require rackunit/chk))

(define (ctype-array? ct)
  (vector? (ctype-basetype ct)))
(define (ctype-array-type ct)
  (vector-ref (ctype-basetype ct) 0))
(define (ctype-array-length ct)
  (vector-ref (ctype-basetype ct) 1))

(define (pointer-count ct)
  (eprintf "~a ~a\n" ct (ctype-basetype ct))
  (cond
    [(eq? _racket ct)
     1]
    [(ctype-array? ct)
     (define at (ctype-array-type ct))
     (eprintf "array ~a ~a\n" ct at)
     (match (pointer-count at)
       [#f #f]
       [pc (* pc (ctype-array-length ct))])]
    [else
     #f]))
(module+ test
  (chk (pointer-count _int) #f
       (pointer-count _racket) 1
       (pointer-count (_array _racket 2)) 2
       (pointer-count (_array _racket 2 4)) 8))

(define (layout->ctime-map l)
  (define-values (rcm rst)
    (for/fold ([cm empty]
               [pre empty])
        ([e (in-list l)])
      (match (pointer-count e)
        [#f
         (values cm
                 (cons e pre))]
        [pc
         (values (cons (cons (reverse pre) pc) cm)
                 empty)])))
  (reverse rcm))

(module+ test
  (require (for-syntax racket/base))
  (define-syntax (t stx)
    (syntax-case stx ()
      [(_ layout ctime-map)
       (quasisyntax/loc stx
         (let ([layout-ev layout]
               [ctime-map-ev ctime-map])
           (chk #,(syntax/loc stx
                    (layout->ctime-map layout-ev))
                ctime-map-ev)))]))

  (t (list)
     (list))
  (t (list _int8 _int)
     (list))
  (t (list _int8 _float _int)
     (list))
  (t (list _int8 _float _int _racket)
     (list (cons (list _int8 _float _int) 1)))
  (t (list _int8 _racket _float _int _racket)
     (list (cons (list _int8) 1) (cons (list _float _int) 1)))
  (t (list _int8 _racket _racket _float _int _racket)
     (list (cons (list _int8) 2) (cons (list _float _int) 1)))
  (t (list _int8 _racket _float _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int) 1)))
  (define _int4 (_array _int 4))
  (t (list _int8 _racket _float _int4 _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int4 _int) 1)))
  (define _int44 (_array _int 4 4))
  (t (list _int8 _racket _float _int44 _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int44 _int) 1)))
  (t (list _int8 _racket _float (_array _racket 8) _int _racket _int)
     (list (cons (list _int8) 1)
           (cons (list _float) 8)
           (cons (list _int) 1)))
  (t (list _int8 _racket _float (_array _racket 2 4) _int _racket _int)
     (list (cons (list _int8) 1)
           (cons (list _float) 8)
           (cons (list _int) 1))))
