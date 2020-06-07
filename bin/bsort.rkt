#!/usr/bin/env racket
#lang racket/base
(require racket/match)

(struct bmt ())
(struct bnode (l x r))

(define (blist t)
  (match t
    [(bmt) '()]
    [(bnode l x r)
     (append (blist l) (cons x (blist r)))]))

(define (binsert t e)
  (match t
    [(bmt) (bnode t e t)]
    [(bnode l x r)
     (if (prefer e x)
       (bnode (binsert l e) x r)
       (bnode l x (binsert r e)))]))

(define (prefer x y)
  (printf "Do you prefer ~s to ~s?\n" x y)
  (read))

(define (bsort l)
  (blist
   (for/fold ([t (bmt)]) ([e (in-list l)])
     (binsert t e))))

(module+ main
  (require racket/cmdline
           racket/file)
  (command-line #:program "bsort"
                #:args (i)
                (for-each displayln (bsort (file->lines i)))))
