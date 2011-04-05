#lang racket/base
(require (for-syntax racket/base)
         racket/class
         racket/function
         racket/runtime-path
         racket/snip)

(define reactive-snip%
  (class* snip% ()
    (init-field sub-snips)
    
    (printf "Snips: ~a\n" sub-snips)
    
    (define (the-snip)
      (list-ref sub-snips
                (modulo (current-seconds) (length sub-snips))))
    
    (define-syntax-rule (delegate id)
      (define/override (id . a)
        (define some-snip (the-snip))
        (printf "Delegating (~a ~a) to ~a\n"
                'id a
                some-snip)
        (send/apply some-snip id a)))
    
    (delegate get-extent)
    (delegate draw)
    (delegate get-text)
    ; set-unmodified or modified
    
    (super-new)))

(define-runtime-path img1 '(lib "PLT-206-larval.png" "icons"))
(define-runtime-path img2 '(lib "PLT-206-mars.jpg" "icons"))

(define sub-snips
      (map (curry make-object image-snip%) 
           (list img1 img2)))

(define x
  (make-object
      reactive-snip% 
    sub-snips))

sub-snips

x