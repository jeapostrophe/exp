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
       (list ref)]
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
       next])))

(define (encode str)
  (for ([p (in-stream str)]
        [refs (in-naturals 0)])
    (define (write-ref ref)
      (cond
        [(<= refs (sub1 (expt 2 8)))
         (write-byte ref)]
        [(<= refs (sub1 (expt 2 16)))
         (write-bytes (integer->integer-bytes ref 2 #f))]
        [else
         (error 'encode "too many refs ~e" refs)]))
    (match p
      [(cons ref b)
       (write-ref ref)
       (write-byte b)]
      [(? number? ref)
       (write-ref ref)])))

(define (decode ip)
  (let loop ([refs 0])
    (define (read-ref ref)
      (cond
        [(<= refs (sub1 (expt 2 8)))
         (read-byte ip)]
        [(<= refs (sub1 (expt 2 16)))
         (integer-bytes->integer (read-bytes 2 ip) #f)]
        [else
         (error 'decode "too many refs ~e" refs)]))
    (define ref (read-ref ip))
    (define b (read-byte ip))
    (if (eof-object? b)
      (stream ref)
      (stream-cons (cons ref b)
                   (loop (add1 refs))))))

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
                    7))
(define output (with-output-to-bytes (λ () (decompress compressed))))
(check-equal? output input)
(define encoded (with-output-to-bytes (λ () (encode compressed))))
(check-equal? encoded
              (bytes 0 A 1 B 2 B 0 B 2 A 5 B 4 B 3 A 7))
(check <= (bytes-length encoded) (bytes-length input))
(define decoded (decode (open-input-bytes encoded)))
(check-equal? (stream->list decoded)
              (stream->list compressed))

(define (compresses? input)
  (define compressed (compress (open-input-bytes input)))
  (define encoded (with-output-to-bytes (λ () (encode compressed))))
  (define decoded (decode (open-input-bytes encoded)))
  (define output (with-output-to-bytes (λ () (decompress compressed))))
  (define encoded-l (bytes-length encoded))
  (define input-l (bytes-length input))
  (check <= encoded-l input-l)
  (check-equal? (stream->list decoded)
                (stream->list compressed))
  (check-equal? output input)
  (exact->inexact (- 1 (/ encoded-l input-l))))

(require racket/file)
(compresses? (file->bytes "lz78.rkt"))
