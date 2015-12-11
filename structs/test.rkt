#lang at-exp racket/base
(require racket/performance-hint
         racket/format
         racket/unsafe/ops
         racket/flonum
         racket/runtime-path
         racket/file
         racket/system
         ffi/unsafe
         racket/contract/region
         (prefix-in c: racket/contract/base))

(define N 18000000)
;; NOTE: Change this to `define` for the second kind of test
(define-syntax-rule (test-fun make get-x get-y)
  (λ ()
    (define it (make 1.0 2.0))
    (for/fold ([sum 0.0])
              ([i (in-range N)])
      (fl+ sum
           (fl+ (get-x it)
                (get-y it))))))
(define-syntax-rule (test id make get-x get-y)
  (module+ test
    (test-it id (test-fun make get-x get-y))))
(define R '())
(define (test-it id fun)
  (define-values (res cpu real gc)
    (time-apply fun '()))
  (set! R (cons (cons id cpu) R))
  (apply values res))

;; Prefab struct
(struct ps (x y) #:prefab)
(test 'prefab-struct ps ps-x ps-y)

;; Struct
(struct s (x y))
(test 'struct s s-x s-y)

;; Struct w/ contract
(with-contract contract-boundary
  ([sc-x (c:-> s? flonum?)]
   [sc-y (c:-> s? flonum?)])
  (define sc-x s-x)
  (define sc-y s-y))
(test 'struct-w/-contract s sc-x sc-y)

;; Unsafe struct
(begin-encourage-inline
  (define (us-x u) (unsafe-struct-ref u 0))
  (define (us-y u) (unsafe-struct-ref u 1)))
(test 'unsafe-struct s us-x us-y)

;; Unsafe struct*
(begin-encourage-inline
  (define (us*-x u) (unsafe-struct*-ref u 0))
  (define (us*-y u) (unsafe-struct*-ref u 1)))
(test 'unsafe-struct* s us*-x us*-y)

;; Vector
(begin-encourage-inline
  (define (v x y) (vector x y))
  (define (v-x u) (vector-ref u 0))
  (define (v-y u) (vector-ref u 1)))
(test 'vector v v-x v-y)

;; Unsafe vector
(begin-encourage-inline
  (define (uv-x u) (unsafe-vector-ref u 0))
  (define (uv-y u) (unsafe-vector-ref u 1)))
(test 'unsafe-vector v uv-x uv-y)

;; Unsafe vector*
(begin-encourage-inline
  (define (uv*-x u) (unsafe-vector*-ref u 0))
  (define (uv*-y u) (unsafe-vector*-ref u 1)))
(test 'unsafe-vector* v uv*-x uv*-y)

;; Flvector
(begin-encourage-inline
  (define (fv x y) (flvector x y))
  (define (fv-x f) (flvector-ref f 0))
  (define (fv-y f) (flvector-ref f 1)))
(test 'flvector fv fv-x fv-y)

;; Unsafe flvector
(begin-encourage-inline
  (define (ufv-x f) (unsafe-flvector-ref f 0))
  (define (ufv-y f) (unsafe-flvector-ref f 1)))
(test 'unsafe-flvector fv ufv-x ufv-y)

;; Cstruct
(define-cstruct _cs
  ([x _double]
   [y _double]))
(test 'cstruct make-cs cs-x cs-y)

;; Unsafe cstruct
;; XXX This doesn't exist

;; Ptr
(begin-encourage-inline
  (define (ptr-x p) (ptr-ref p _double 0))
  (define (ptr-y p) (ptr-ref p _double 1)))
(test 'ptr make-cs ptr-x ptr-y)

;; Unsafe ptr
;; XXX This doesn't exist

;; Call out to C individually
(define C-LIB-SOURCE
  @~a{
typedef struct { double x; double y; } thestruct;
double get_x ( thestruct *u ) { return u->x; }
double get_y ( thestruct *u ) { return u->y; }
})

(define-runtime-path C-LIB-SOURCE-PATH "lib.c")
(define-runtime-path C-LIB-SO-PATH "lib.so")
(display-to-file C-LIB-SOURCE C-LIB-SOURCE-PATH #:exists 'replace)
(system @~a{cc @C-LIB-SOURCE-PATH -shared -o @C-LIB-SO-PATH})
(define the-lib (ffi-lib C-LIB-SO-PATH))
(begin-encourage-inline
  (define c-x (get-ffi-obj 'get_x the-lib (_fun _cs-pointer -> _double)))
  (define c-y (get-ffi-obj 'get_y the-lib (_fun _cs-pointer -> _double))))
(test 'c make-cs c-x c-y)

;; Call out to C for whole test
(define C-TEST-SOURCE
  @~a{
@C-LIB-SOURCE
double go () {
 thestruct it = { .x = 1.0, .y = 2.0 };
 double sum = 0.0;
 for ( int i = 0; i < @N; i++ ) {
   sum = sum + get_x(&it) + get_y(&it);
 }
 return sum;
}
})
(define-runtime-path C-TEST-SOURCE-PATH "test.c")
(define-runtime-path C-TEST-SO-PATH "test.so")
(display-to-file C-TEST-SOURCE C-TEST-SOURCE-PATH #:exists 'replace)
(system @~a{cc -O3 @C-TEST-SOURCE-PATH -shared -o @C-TEST-SO-PATH})
(define the-test (ffi-lib C-TEST-SO-PATH))
(define the-test-go (get-ffi-obj 'go the-test (_fun -> _double)))
(test-it 'c-test (λ () (the-test-go)))

;;;;;;;;;;
(module+ test
  (for ([id*cpu (in-list (sort R <= #:key cdr))])
    (displayln (~a (~a #:min-width 20 (car id*cpu)) ": "
                   (cdr id*cpu)))))
