#lang racket/base
(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/list)
         racket/list
         racket/match)

;; encode : value -> bytes
;; decode : bytes -> value

;; --->

;; encode : (v:value) ->
;;       (vbs:bytes) (list (pairs points-from encode-thunk))
;; decode : (heap:bytes) (start:addr)           -> value

(struct addr*thunk (addr thunk))
(struct branch (left right))

;; xxx if we knew total size, we'd make this mutating
(define (stitch vbs addr*et-tree)
  (match addr*et-tree
    [(list)
     vbs]
    [(list-rest (addr*thunk addr et) more)
     (define start (bytes-length vbs))
     (define-values (et-bs et-mores) (et))
     (define nbs (bytes-append vbs et-bs))
     ;; Replace addr in nbs with addr (patch)
     (integer->integer-bytes start 4 #f #t nbs addr)
     (stitch nbs (branch more et-mores))]
    [(branch (branch left-left-b left-right-b) right-b)
     (stitch vbs (branch left-right-b
                         (branch left-right-b
                                 right-b)))]
    [(branch (list) right-tree)
     (stitch vbs right-tree)]
    [(branch (list-rest first-on-left rest-of-left) right-tree)
     (stitch vbs
             (cons first-on-left
                   (branch rest-of-left
                           right-tree)))]))

(define (encode-closure encode v)
  (define-values (fbs post-tree) (encode v))
  (stitch fbs post-tree))

(define-syntax branch*
  (syntax-rules ()
    [(_) empty]
    [(_ o) o]
    [(_ o t) (branch o t)]
    [(_ o t ...) (branch o (branch* t ...))]))

(begin-for-syntax
  (define-syntax-class spec
    #:attributes (encode decode size)
    [pattern
     ((~literal vector) e:spec ...
      (~optional (~seq #:align align-e:expr)))
     #:attr size
     (apply + (attribute e.size))
     #:attr encode
     (with-syntax
         ([((i e.bs e.tree) ...)
           (for/list ([i (in-naturals)]
                      [e (in-list (syntax->list #'(e ...)))])
             (list i
                   (generate-temporary)
                   (generate-temporary)))])
       #'(λ (v)
           (let-values ([(e.bs e.tree)
                         (e.encode (vector-ref v i))]
                        ...)
             (values
              (bytes-append
               e.bs
               ...)
              ;; e.tree contains 0 everywhere but should be offset by
              ;; e.start either do that here or later (in stitch)
              ;; OR
              ;; heap place-to-write value -> void
              (branch* e.tree ...)))))
     #:attr decode
     (with-syntax
         ([((e.start e.end) ...)
           (let ()
             (define-values (final-end e.start-in-reverse)
               (for/fold ([last-end 0] [ans empty])
                   ([e.size (in-list (attribute e.size))])
                 (define my-start last-end)
                 (define my-end (+ my-start e.size))
                 (values my-end
                         (list* (list my-start my-end) ans))))
             (reverse e.start-in-reverse))])
       #'(λ (bs)
           (vector (e.decode (subbytes bs e.start e.end))
                   ...)))]
    [pattern
     (~literal float)
     #:attr size 4
     #:attr encode
     #'(λ (v) (values (real->floating-point-bytes v 4) empty))
     #:attr decode
     #'(λ (bs) (floating-point-bytes->real bs 4))]
    [pattern
     other-s
     #:declare other-s (static spec-info? "spec")
     #:attr size
     (spec-info-size (attribute other-s.value))
     #:attr encode
     (spec-info-encode-id (attribute other-s.value))
     #:attr decode
     (spec-info-decode-id (attribute other-s.value))]
    [pattern
     ((~literal pointer) i:spec)
     #:attr size
     (+ 4 (attribute i.size))
     #:attr encode
     #'(λ (v)
         (values (integer->integer-bytes 0 4 #f #t)
                 (list (addr*thunk
                        0
                        (λ ()
                          (i.encode v))))))
     #:attr decode
     #'(λ (bs start)
         (i.decode bs
                   (integer-bytes->integer
                    bs #f #t start (+ start 4))))]))

(begin-for-syntax
  (struct spec-info (encode-id decode-id size)))

(define-syntax (define-spec stx)
  (syntax-parse stx
    [(_ (n:id e:id d:id) s:spec)
     (quasisyntax/loc stx
       (begin
         (define-syntax n
           (spec-info #'e #'d
                      #,(attribute s.size)))
         (define e s.encode)
         (define d s.decode)))]))

;; (define-spec
;;   (4f-encode 4f-decode)
;;   (let ([quaternion
;;          (vector float float float float
;;                  #:align 16)])
;;     (vector quaternion quaternion)))

(define-spec
  (4f 4f-encode 4f-decode)
  (vector float float float float
          #:align 16))

(define-syntax (define-specs stx)
  (syntax-parse stx
    [(_ [sc s] ...)
     (with-syntax
         ([((sc-encode sc-decode)
            ...)
           (for/list ([sc (in-list (syntax->list #'(sc ...)))])
             (list (format-id sc "~a-encode" sc)
                   (format-id sc "~a-decode" sc)))])
       (syntax/loc stx
         (begin
           (define-spec (sc sc-encode sc-decode) s)
           ...)))]))

(define-specs
  [quaternion
   (vector float float float float
           #:align 16)]
  [dq
   (vector quaternion quaternion)]
  [dq-p
   (vector (pointer quaternion) (pointer quaternion))]
  )

(module+ test
  (require rackunit)
  (encode-closure 4f-encode (vector 0.0 0.0 0.0 0.0))
  (4f-decode #"\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0\0")
  (encode-closure 4f-encode
                  (vector 0.0 0.5 0.0 4.0))
  (encode-closure dq-encode
                  (vector (vector 0.0 0.5 0.0 4.0)
                          (vector 1.1 0.5 0.4 4.0)))
  (encode-closure dq-p-encode
                  (vector (vector 0.0 0.5 0.0 4.0)
                          (vector 1.1 0.5 0.4 4.0))))
