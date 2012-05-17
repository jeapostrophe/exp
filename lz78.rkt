#lang racket/base
(require racket/list
         racket/match
         racket/stream
         racket/port)

;; Based on the example at the top of
;; https://en.wikipedia.org/wiki/LZ77 on 2012/05/17
(define (compress ip)
  (define dict (make-hasheq))
  (define (search-for-shortest this)
    (let loop ([dict dict]
               [last 0])
      (define b (read-byte ip))
      (cond
        [(eof-object? b)
         (cons last 0)]
        [(hash-ref dict b #f)
         =>
         (λ (next)
           (loop (cdr next) (car next)))]
        [else
         (hash-set! dict b (cons this (make-hasheq)))
         (cons last b)])))
  (let outer-loop ([next 1])
    (define W (search-for-shortest next))
    (match W
      [(cons ref 0)
       (stream W)]
      [(cons ref c)
       (stream-cons W (outer-loop (add1 next)))])))

(define (decompress seq)
  (void))

(require rackunit)
(define input #"AABABBBABAABABBBABBABB")
(define compressed (compress (open-input-bytes input)))
(define A (char->integer #\A))
(define B (char->integer #\B))
(check-equal? (stream->list compressed)
              (list (cons 0 A)
                    (cons 1 B)
                    (cons 2 B)
                    (cons 0 B)
                    (cons 2 A)
                    (cons 5 B)
                    (cons 4 B)
                    (cons 3 A)
                    (cons 7 0)))
(define output (with-output-to-bytes (λ () (decompress compressed))))
(check-equal? output input)
