#lang racket/base
(require racket/match
         racket/list
         racket/function
         racket/port)

(struct node (label props content children) #:transparent)

;; Reading
(define (trim-spaces s)
  (regexp-replace* #rx" +$"
                   (regexp-replace* #rx"^ +" s "")
                   ""))
(define (strip-stars s)
  (trim-spaces (regexp-replace #rx"^\\*+ " s "")))

(define (read-content)
  (define c (peek-char))
  (cond
   [(or (eof-object? c)
        (equal? #\* c))
    empty]
   [else
    (list* (regexp-replace #rx"^[ \t]+" (read-line) "")
           (read-content))]))

(define (extract-properties ls)
  (define-values 
    (content/rev props in-props?)
    (for/fold
     ([content/rev empty]
      [props (hash)]
      [in-props? #f])
     ([l (in-list ls)])
     (cond
      [in-props?
       (match 
        l
        [(regexp #rx"^:([^:]+):[ \t]+(.*)$" (list _ key (app trim-spaces val)))
         (values content/rev
                 (if (string=? "" val)
                     props
                     (hash-set props key val))
                 #t)]
        [":END:"
         (values content/rev
                 props
                 #f)])]
      [(string=? ":PROPERTIES:" l)
       (values content/rev
               props
               #t)]
      [else
       (values (list* l content/rev)
               props
               #f)])))
  (values props
          (reverse content/rev)))

(define (stars i)
  (string-append (make-string i #\*) " "))

(define (read-level i)
  (cond
   [(equal? (stars i)
            (peek-string (add1 i) 0))
    (define s (read-line))
    (define-values (props content)
      (extract-properties (read-content)))
    (list*
     (node (strip-stars s)
           props
           content
           (read-level (add1 i)))
     (read-level i))]
   [else
    empty]))

(define (read-org)
  (read-level 1))

;; Write
(define (write-node i n)
  (match-define (node label props/null content children) n)
  (define props
    (for/fold ([ht (hasheq)])
        ([(k v) (in-hash props/null)])
      (if v
        (hash-set ht k v)
        ht)))
  (define indent (make-string (+ 1 i) #\space))
  (printf "~a~a\n" (stars i) label)
  (unless (zero? (hash-count props))
          (printf "~a:PROPERTIES:\n" indent)
          (for ([k (in-list (sort (hash-keys props) string<=?))])
               (define v (hash-ref props k))
               (printf "~a:~a:\t~a\n" indent k v))
          (printf "~a:END:\n" indent))
  (for ([c (in-list content)])
       (if (regexp-match #rx"^#\\+" c)
           (printf "~a\n" c)
           (printf "~a~a\n" indent c)))
  (for-each (curry write-node (add1 i)) children))

(define (write-org ns)
  (for-each (curry write-node 1) ns))

;; XXX contracts
(provide read-org
         write-org
         (struct-out node))
