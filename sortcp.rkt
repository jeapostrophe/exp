#lang racket
(require racket/cmdline)

(define dry? #f)
(define-syntax-rule (dry (f a ...))
  (begin
    (printf "~a\n" (list 'f a ...))
    (unless dry?
      (f a ...))))

(define (sort-char s)
  (define c (string-ref s 0))
  (if (char-alphabetic? c)
      (string (char-upcase c))
      "#"))

(define-values (from to)
  (command-line #:program "sortcp"               
                #:args (from to) (values from to)))

(define fs (sort (directory-list from)
                 string-ci<=?
                 #:key path->string))

(define exists? (make-hash))
(for ([f (in-list fs)]
      #:when (file-exists? (build-path from f)))
  (define first-char (sort-char (path->string f)))
  (define src (build-path from f))
  (define dir (build-path to first-char))
  (define dest (build-path dir f))
  (unless (hash-has-key? exists? first-char)
    (dry (make-directory dir))
    (hash-set! exists? first-char #t))
  (dry (copy-file src dest)))