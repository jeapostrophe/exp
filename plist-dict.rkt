#lang racket/base
(require racket/match
         racket/list
         racket/dict)

(define pl-expr->value
  (match-lambda
   [(? string? s)
    s]
   [(list 'true)
    #t]
   [(list 'false)
    #f]
   [(list 'integer i)
    i]
   [(list 'real r)
    r]
   [(list 'array pl-expr ...)
    (list->vector (map pl-expr->value pl-expr))]
   [(list 'dict assoc-pair ...)
    (define (assoc-pair-add ap dict)
      (match-define (list 'assoc-pair string pl-expr) ap)
      (dict-set dict string (pl-expr->value pl-expr)))
    (foldl assoc-pair-add empty assoc-pair)]))

(define value->pl-expr
  (match-lambda
   [(? string? s)
    s]
   [#t
    (list 'true)]
   [#f
    (list 'false)]
   [(? integer? i)
    (list 'integer i)]
   [(? real? r)
    (list 'real r)]
   [(? vector? pl-expr)
    (list* 'array (map value->pl-expr (vector->list pl-expr)))]
   [(? dict? d)
    (list* 'dict
           (for/list ([(k v) (in-dict d)])
             (list 'assoc-pair k (value->pl-expr v))))]))

(module+ test
  (require rackunit
           racket/pretty)

  (define my-dict
    `(dict (assoc-pair "first-key"
                       "just a string with some  whitespace")
           (assoc-pair "second-key"
                       (false))
           (assoc-pair "third-key"
                       (dict))
           (assoc-pair "fourth-key"
                       (dict (assoc-pair "inner-key"
                                         (real 3.432))))
           (assoc-pair "fifth-key"
                       (array (integer 14)
                              "another string"
                              (true)))
           (assoc-pair "sixth-key"
                       (array))))
  (pretty-print my-dict)

  (define my-dict-val (pl-expr->value my-dict))
  (pretty-print my-dict-val)

  (check-equal? my-dict
                (value->pl-expr my-dict-val)))
