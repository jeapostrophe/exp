#lang racket/base

;; http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/

(struct parser (precedence impl)
  #:property prop:procedure
  (struct-field-index impl))

(define PREFIXES
  (hasheq))
(define INFIXES
  (hasheq))

(define default-prefix #f)
(define default-infix #f)

(define (parse* p lvl)
  (define token (read-char p))
  (define prefix-p (hash-ref PREFIXES token default-prefix))
  (let loop ([left (prefix-p p lvl token)])
    (cond
      [(< lvl (get-level p))
       (define token (read-char p))
       (define infix-p (hash-ref INFIXES token default-infix))
       (loop (infix-p p lvl left token))]
      [else
       left])))

(define (get-level p)
  (parser-precedence
   (hash-ref INFIXES (peek-char p) default-infix)))

(define (parse s)
  (parse* (open-input-string s) +inf.0))

(module+ test
  (require chk)
  (define (pchk s e)
    (chk (parse s) e))
  
  (pchk "a - b - c"
        '(- (- a b) c))
  (pchk "define : f(s) = 
         | printf(\"hi ~a\n\", s),
           \"hi\"
         | f(s, x) = f(x + y)"
        'xxx))
