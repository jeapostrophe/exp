#lang racket/base
(require (only-in '#%foreign ctype-basetype)
         racket/list
         racket/match
         ffi/unsafe)
(module+ test
  (require rackunit/chk))

(define (ctype-flatten ct)
  (define bt (ctype-basetype ct))
  (cond
    [(ctype? bt)
     (ctype-flatten bt)]
    [(list? bt)
     (append-map ctype-flatten bt)]
    [(vector? bt)
     (define btf (ctype-flatten (vector-ref bt 0)))
     (append* (for/list ([i (in-range (vector-ref bt 1))])
                btf))]
    [else
     (list ct)]))

(define (ctype->ctime-map ct)
  (define l (ctype-flatten ct))
  (define-values (rcm rst)
    (for/fold ([cm empty]
               [pre empty])
        ([e (in-list l)])
      (if (eq? _racket e)
        (if (and (empty? pre) (cons? cm))
          (values (cons (cons (car (first cm))
                              (add1 (cdr (first cm))))
                        (rest cm))
                  empty)
          (values (cons (cons (reverse pre)
                              1)
                        cm)
                  empty))
        (values cm
                (cons e pre)))))
  (reverse rcm))

;; xxx alignment?
(define (ctime-map->rtime-map cm)
  (for/list ([p (in-list cm)])
    (cons (for/sum ([ct (in-list (car p))])
                   (ctype-sizeof ct))
          (cdr p))))

(define SIZE 1)
(define (span->integer-bytes s)
  (if (= SIZE 1)
    (bytes s)
    (integer->integer-bytes s SIZE #f)))
(define (rtime-map->bytes rm)
  (apply
   bytes-append
   (map span->integer-bytes
        (append-map (λ (c) (list (car c) (cdr c))) rm))))

(module+ test
  (require (for-syntax racket/base))
  (define-syntax (t stx)
    (syntax-case stx ()
      [(_ layout ctime-map rtime-map bs)
       (quasisyntax/loc stx
         (let ([ct-v (make-cstruct-type layout)]
               [ctime-map-ev ctime-map]
               [rtime-map-ev rtime-map]
               [bs-ev bs])
           (chk #,(syntax/loc stx
                    (ctype->ctime-map ct-v))
                ctime-map-ev
                #,(syntax/loc stx
                    (ctime-map->rtime-map ctime-map-ev))
                rtime-map-ev
                #,(syntax/loc stx
                    (rtime-map->bytes rtime-map-ev))
                bs-ev)))]))

  (t (list _int)
     (list)
     (list)
     (bytes))
  (t (list _int8 _int)
     (list)
     (list)
     (bytes))
  (t (list _int8 _float _int)
     (list)
     (list)
     (bytes))
  (t (list _int8 _float _int _racket)
     (list (cons (list _int8 _float _int) 1))
     (list (cons (+ 1 4 4) 1))
     (bytes (+ 1 4 4) 1))
  (t (list _int8 _racket _float _int _racket)
     (list (cons (list _int8) 1) (cons (list _float _int) 1))
     (list (cons (+ 1) 1) (cons (+ 4 4) 1))
     (bytes (+ 1) 1 (+ 4 4) 1))
  (t (list _int8 _racket _racket _float _int _racket)
     (list (cons (list _int8) 2) (cons (list _float _int) 1))
     (list (cons (+ 1) 2) (cons (+ 4 4) 1))
     (bytes (+ 1) 2 (+ 4 4) 1))
  (t (list _int8 _racket _float _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int) 1))
     (list (cons (+ 1) 1) (cons (+ 4 4) 1))
     (bytes (+ 1) 1 (+ 4 4) 1))
  (t (list _int8 _racket _float (_array _int 4) _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int _int _int _int _int) 1))
     (list (cons (+ 1) 1) (cons (+ 4 (* 5 4)) 1))
     (bytes (+ 1) 1 (+ 4 (* 5 4)) 1))
  (t (list _int8 _racket _float (_array _int 2 2) _int _racket _int)
     (list (cons (list _int8) 1) (cons (list _float _int _int _int _int _int) 1))
     (list (cons (+ 1) 1) (cons (+ 4 (* 5 4)) 1))
     (bytes (+ 1) 1 (+ 4 (* 5 4)) 1))
  (t (list _int8 _racket _float (_array _racket 8) _int _racket _int)
     (list (cons (list _int8) 1)
           (cons (list _float) 8)
           (cons (list _int) 1))
     (list (cons (+ 1) 1)
           (cons (+ 4) 8)
           (cons (+ 4) 1))
     (bytes 1 1 4 8 4 1))
  (t (list _int8 _racket _float (_array _racket 2 4) _int _racket _int)
     (list (cons (list _int8) 1)
           (cons (list _float) 8)
           (cons (list _int) 1))
     (list (cons (+ 1) 1)
           (cons (+ 4) 8)
           (cons (+ 4) 1))
     (bytes 1 1 4 8 4 1)))

(define x (make-cstruct-type (list _int8 _int)))
(ctype-basetype x)
(ctype-sizeof x)
(ctype-alignof x)
(ctype->layout x)
