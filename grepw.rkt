#!/bin/sh
#| -*- scheme -*-
exec racket -um "$0" "$@"
|#
#lang racket
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

(define-lex-abbrev target
  (:: (:or #\c #\C) (:or #\l #\L)
      (:* (:~ (:or #\( #\) #\" whitespace)))))

(define cl-lexer
  (lexer
   [(eof) eof]
   [target lexeme]
   [any-char (cl-lexer input-port)]))

(define (cl-lexer* p)
  (for/list ([e (in-producer (λ () (cl-lexer p)) eof-object?)])
    e))

(define (test)
  (list
   (cl-lexer* (open-input-string "clFoo"))
   (cl-lexer* (open-input-string "clFoo("))
   (cl-lexer* (open-input-string "(clFoo"))
   (cl-lexer* (open-input-string "clFoo blog"))
   (cl-lexer* (open-input-string " clFoo blog"))
   (cl-lexer* (open-input-string "bloo clFoo blog"))
   (cl-lexer* (open-input-string "bloo clFoo( blog"))
   (cl-lexer* (open-input-string "bloo (clFoo blog"))))

#;(test)

(define (main . fs)
  (for ([f (in-list fs)])
    (call-with-input-file* f
      (λ (p)
        (for-each displayln (cl-lexer* p))))))

(provide main)