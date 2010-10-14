#lang typed/racket
(define-type Inputs (Listof Real))
(define-type Digits (Listof Integer))
(define-type Frequencies (Listof (Pair Integer Number)))

(: freq (Digits -> Frequencies))
(define (freq l)
  (define h (make-vector 10 0))
  (define tot
    (for/fold:
     : Integer ([tot : Integer 0]) 
     ([e : Integer (in-list l)])
     (vector-set! h e (add1 (vector-ref h e)))
     (add1 tot)))
  (for/list: : Frequencies
   ([e : Integer (in-range 10)]
    [c : Integer (in-vector h)])
   (cons e (/ c tot))))

(: nums->digits (Inputs -> Digits))
(define (nums->digits l)
  (for/list: : Digits
   ([x : Real (in-list l)])
   (define z (if (x . < . 0) (- x) x))
   (- (char->integer
       (string-ref (real->decimal-string z) 0))
      (char->integer #\0))))

(: benford (Inputs -> Frequencies))
(define (benford l)
  (freq (nums->digits l)))

(equal?
 (benford 
  (list 1/10 0.2 0.3 0.4 5/10 0.6 0.7 0.8 0.9 0.10
        11 12 13 -14 15 16 17 18 19
        21 -22 23 24 25 26 27 28
        31 32 -33 34 35 36 37
        41 42 43 44 45 46
        51 -52 54 54 55
        61 62 -63 64
        71 -72 73
        81 82
        91))
 (for/list: : Frequencies
  ([i : Integer (in-range 10)])
  (cons i
        (/ (- 10 i)
           (+ 10 9 8 7 6 5 4 3 2 1)))))