#lang racket/base
(require "module.rkt")

;; A normal `module` declaration can use a different module-language
(module og-duck racket/base
  (provide num-eggs quack)
  (define num-eggs 2)
  (define (quack n)
    (unless (zero? n)
      (printf "quack\n")
      (quack (sub1 n)))))
;; And be required by the parent module
(require (prefix-in og: 'og-duck))
(og:quack og:num-eggs)

;; module+ can't do this though, because there's nowhere to write down
;; that you don't want to use (module* .... #f ....)
(module+ tests
  (printf "Old module+..."))

(module+ tests
  (printf "works!\n"))

;; define-module+ lets you define a new `module+` like form
;; specialized for a particular module. This, however, is like
;; `module` and not `module*`, so it can't require the parent
(define-module+ duck+
  ;; You tell it what the name of the module to define is
  duck
  ;; And what the module language is
  racket/base)

;; Now we start filling in the module
(duck+ (provide num-eggs quack)
       (define num-eggs 2))
(duck+ (define (quack n)
         (unless (zero? n)
           (printf "quack\n")
           (quack (sub1 n)))))

;; Since this is a 'module', we need to finish declaring it at some
;; point if we want the parent to get it. If we didn't want that, we
;; wouldn't need to use this form.
(duck+ #:declared)

;; So, here we can get at it:
(require 'duck)
(quack num-eggs)

;; This is a syntax error because `duck` is declared
#;(duck+ (printf "Yo!\n"))

(define nine 9)
(provide nine)

;; We can, of course, defined a `module*` like this.
(define-module*+ main+
  main racket/base)
(main+ (require (submod "..")))
(main+ (displayln nine))
;; We aren't required to put in #:declared and probably never would
;; for `define-module*+`

