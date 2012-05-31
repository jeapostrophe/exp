#lang racket/base
(require racket/match)

(define plist-dict->hash
  (match-lambda
   [(list 'dict assoc-pair ...)
    (foldl assoc-pair-add (hash) assoc-pair)]))

(define (assoc-pair-add ap dict)
  (match-define (list 'assoc-pair string pl-expr) ap)
  (hash-set dict string (pl-expr->value pl-expr)))

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
    (map pl-expr->value pl-expr)]
   [dict-expr
    (plist-dict->hash dict-expr)]))

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

(define my-dict-val 
  (pl-expr->value my-dict))

(require racket/pretty)
(pretty-print my-dict-val)

(define (hash->plist-dict ht)
  (list* 'dict
         (for/list ([(k v) (in-hash ht)])
           (list 'assoc-pair k (value->pl-expr v)))))

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
   [(? list? pl-expr)
    (list 'array (map value->pl-expr pl-expr))]
   [dict-expr
    (hash->plist-dict dict-expr)]))

(value->pl-expr my-dict-val)
