#lang racket
(require "snip.rkt"
         racket/snip
         racket/runtime-path)

(define-runtime-path img1 '(lib "PLT-206-larval.png" "icons"))
(define-runtime-path img2 '(lib "PLT-206-mars.jpg" "icons"))

(define sub-snips
  (append
   (map (curry make-object image-snip%) 
        (list img1 img2))
   (list (make-object string-snip% "Test"))))

(define x
  (make-object
      reactive-snip% 
    (first sub-snips)))

(thread
 (λ ()
   (for ([s (in-cycle sub-snips)])
     (send x update! s)
     (sleep 1))))

x