#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         syntax/parse/define)

;; Run-time
(struct state (a b c d) #:transparent)
(define mt (state #f #f #f #f))
(define-simple-macro (set-field st:expr f:id v:expr)
  (struct-copy state st [f v]))
(define-simple-macro (set-field* f:id v:expr)
  (λ (st) (set-field st f v)))

;; Compile-time
(begin-for-syntax
  (define-struct modifier (f)))

(define-simple-macro (define-modifier (m . args) body)
  (begin
    (define-syntax m-f
      (syntax-parser [(_ args) #'body]))
  (define-syntax m (modifier #'m-f))))

(define-modifier (the-a-says x:string)
  (set-field* a x))
(define-modifier (the-b-says 'x:id)
  (set-field* b 'x))
(define-modifier (the-c-is x:string)
  (set-field* c x))
(define-modifier (the-d-looks-like x:nat)
  (set-field* d x))

(define-syntax-parser term
  [(_ ((~var m (static modifier? "state modifier")) . args))
   #:with f (modifier-f (attribute m.value))
   #'(f args)])

(define-syntax-parser program
  [(_) #'mt]
  [(_ x . more) #'((term x) (program . more))])

;; Example
(program
 (the-a-says "Aaah")
 (the-b-says 'Baah)
 (the-c-is "Caaah")
 (the-d-looks-like 42))
