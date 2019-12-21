#lang racket/base
(require (for-syntax racket/base)
         racket/list
         racket/gui/base
         syntax/parse/define
         pict
         racket/match
         racket/pretty)

(define (show-plan p)
  (show-pict p))

(define o->color
  (hasheq 8 "red" 6 "orange" 7 "yellow" 5 "green" 4 "blue" 3 "purple"))

(define-syntax-parser mlet
  [(_ () e:expr) #'e]
  [(_ ([x:id xe:expr] . more) e)
   #'(let ([x xe]) (and x (mlet more e)))])

(define (plan w h opts)
  (cond
    [(or (zero? w) (zero? h))
     (blank)]
    [else
     (define new-opts
       (filter (λ (o) (and (<= o w) (<= o h))) opts))
     (define order (shuffle new-opts))
     (eprintf "~a, ~a ---> ~a\n" w h order)
     (for/or ([o (in-list order)])
       (mlet ([br (plan (- w o) (- h o) order)]
              [dr (plan w (- h o) order)]
              [dd (plan (- w o) h order)])
             (ht-append
              (vl-append (block o)
                         dd)
              (vl-append dr br))))]))

(define (block o)
  (filled-rectangle o o #:color (hash-ref o->color o)))

(module+ main
  (define strip1
    (ht-append (block 8)
               (block 8)
               (block 4)
               (block 8)
               (block 8)))
  (define hstrip1 (scale strip1 0.5))
  (define strip2 strip1)
  (define strip3 strip1)
  (define strip4 strip1)
  (define strip5 strip1)
  (define strip6 strip1)
  (define quilt
    (vl-append
     strip1
     strip2
     hstrip1
     strip3
     strip4
     strip5
     strip6))
  (printf "~a x ~a\n"
          (pict-width quilt)
          (pict-height quilt))
  (show-pict (scale quilt 10)))
