#lang racket/base
(require racket/list
         racket/pretty
         racket/match
         racket/stream
         racket/port)

;; Based on the example at the top of
;; https://en.wikipedia.org/wiki/LZ77 on 2012/05/17
(define (compress ip)
  (define top-dict (make-hasheq))
  (define (search-for-shortest this)
    (let loop ([dict top-dict]
               [last 0])
      (define b (read-byte ip))
      (cond
        [(eof-object? b)
         (begin0 last
                 (pretty-print top-dict))]
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
      [(? number? ref)
       (stream ref)]
      [(cons ref c)
       (stream-cons W (outer-loop (add1 next)))])))

(define (decompress str)
  (define dict (make-hasheq))
  (define (output-from-dict this)
    (match (hash-ref dict this #f)
      [#f
       (void)]
      [(cons last this-b)
       (output-from-dict last)
       (write-byte this-b)]))
  (for/fold ([next 1])
      ([p (in-stream str)])
    (match p
      [(cons ref b)
       (hash-set! dict next p)
       (output-from-dict next)
       (add1 next)]
      [(? number? ref)
       (output-from-dict ref)
       next]))
  (pretty-print dict (current-error-port)))

(define one-max (sub1 (expt 2 (* 8 1))))
(define two-max (sub1 (expt 2 (* 8 2))))
(define four-max (sub1 (expt 2 (* 8 4))))
(define eight-max (sub1 (expt 2 (* 8 8))))
(define (refs->len refs)
  (cond
    [(<= refs two-max) 2]
    [(<= refs four-max) 4]
    [(<= refs eight-max) 8]
    [else
     (error 'encode "too many refs ~e" refs)]))

(define (encode str)
  (define encode-bytes (make-bytes 8))
  (define op (current-output-port))
  (for ([p (in-stream str)]
        [refs (in-naturals 0)])
    (define (write-ref ref)
      (cond
        [(<= refs one-max)
         (write-byte ref)]
        [else
         (define len (refs->len refs))
         (integer->integer-bytes ref len #f #f encode-bytes)
         (write-bytes encode-bytes op 0 len)]))
    (match p
      [(cons ref b)
       (write-ref ref)
       (write-byte b)]
      [(? number? ref)
       (write-ref ref)])))

(define (decode ip)
  (define decode-bytes (make-bytes 8))
  (let loop ([refs 0])
    (define (read-ref ref)
      (cond
        [(<= refs one-max)
         (read-byte ip)]
        [else
         (define len (refs->len refs))
         (read-bytes! decode-bytes ip 0 len)
         (integer-bytes->integer decode-bytes #f #f 0 len)]))
    (define ref (read-ref ip))
    (define b (read-byte ip))
    (if (eof-object? b)
      (stream ref)
      (stream-cons (cons ref b)
                   (loop (add1 refs))))))

(require rackunit)

(define (stream-equal? s0 s1)
  (cond
    [(stream-empty? s0)
     (stream-empty? s1)]
    [(stream-empty? s1)
     #f]
    [else
     (and (equal? (stream-first s0)
                  (stream-first s1))
          (stream-equal? (stream-rest s0)
                         (stream-rest s1)))]))

(define (compresses? input
                     #:compressed [compressed-expected #f]
                     #:encoded [encoded-expected #f])
  (define compressed (compress (open-input-bytes input)))
  (when compressed-expected
    (check-true (stream-equal? compressed
                               compressed-expected)))
  (define encoded (with-output-to-bytes (λ () (encode compressed))))
  (when encoded-expected
    (check-equal? encoded encoded-expected))
  (define decoded (decode (open-input-bytes encoded)))
  (check-true (stream-equal? decoded
                             compressed))
  (define encoded-l (bytes-length encoded))
  (define input-l (bytes-length input))
  (check <= encoded-l input-l)
  (define output (with-output-to-bytes (λ () (decompress compressed))))
  (check-true (equal? output input))
  (list encoded-l input-l
        (exact->inexact (- 1 (/ encoded-l input-l)))))

(require racket/file)
(define A (char->integer #\A))
(define B (char->integer #\B))
(compresses? #"AABABBBABAABABBBABBABB"
             #:compressed
             (stream (cons 0 A)
                     (cons 1 B)
                     (cons 2 B)
                     (cons 0 B)
                     (cons 2 A)
                     (cons 5 B)
                     (cons 4 B)
                     (cons 3 A)
                     7)
             #:encoded
             (bytes 0 A 1 B 2 B 0 B 2 A 5 B 4 B 3 A 7))
(compresses? (file->bytes "lz78.rkt"))

(compresses? (bytes 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19))

(compresses? (bytes 0 0))

;; XXX This example uses too much memory. Maybe if I streamed the
;; compressed output better and didn't need to create the whole thing
;; ever.
;;(time (compresses? (file->bytes "/home/jay/Dev/scm/plt/bin/racket")))
