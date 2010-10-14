#lang typed/racket
(define (freq l)
  (define h (make-vector 10 0))
  (define tot
    (for/fold ([tot 0]) ([e (in-list l)])
      (dict-update! h e add1)
      (add1 tot)))
  (for/list ([(e c) (in-dict h)])
    (cons e (/ c tot))))
(define nums->digits
  (curry map
         (compose string->number
                  string
                  (λ (x) (string-ref x 0))
                  number->string
                  (λ (x) (if (x . < . 0) (- x) x)))))
(define (sk l)
  (freq (nums->digits l)))
(define (sort-em l)
  (sort l >= #:key cdr))

(equal?
 (sort-em
  (sk (list 0.1 0.2 0.3 0.4 0.5 0.6 0.7 0.8 0.9 0.10
            11 12 13 -14 15 16 17 18 19
            21 -22 23 24 25 26 27 28
            31 32 -33 34 35 36 37
            41 42 43 44 45 46
            51 -52 54 54 55
            61 62 -63 64
            71 -72 73
            81 82
            91)))
 (for/list ([i (in-range 10)])
   (cons i
         (/ (- 10 i)
            (+ 10 9 8 7 6 5 4 3 2 1)))))