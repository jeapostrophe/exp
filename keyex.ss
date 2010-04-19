#lang scheme
(require "keystruct.ss")

(define-struct crazy (car) #:transparent)
(define-struct (kons crazy) (car cdr) #:transparent)

; Not an id
#;(struct-keyword-constructor 1)

; Not syntax id
#;(struct-keyword-constructor kons-car)

; Not structure info value
(define-syntax foo 1)
#;(struct-keyword-constructor foo)

(define make-kons/key (struct-keyword-constructor kons))

(make-kons/key #:crazy-car 0
               #:kons-car 1
               #:kons-cdr 2)