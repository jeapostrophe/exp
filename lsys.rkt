#lang racket
(require tests/eli-tester)

(define algae
  (match-lambda
   ['a '(a b)]
   ['b '(a)]
   [x (list x)]))

(define (eval-lsys char->string gens start)
  (if (zero? gens)
      start
      (eval-lsys char->string (sub1 gens) (append-map char->string start))))

(test
 (eval-lsys algae 0 '(a)) => '(a)
 (eval-lsys algae 1 '(a)) => '(a b)
 (eval-lsys algae 2 '(a)) => '(a b a)
 (eval-lsys algae 3 '(a)) => '(a b a a b)
 (eval-lsys algae 4 '(a)) => '(a b a a b a b a)
 (eval-lsys algae 5 '(a)) => '(a b a a b a b a a b a a b)
 (eval-lsys algae 6 '(a)) => '(a b a a b a b a a b a a b a b a a b a b a))

(define (eval-turtle char->trans state string)
  (if (empty? string)
      state
      (eval-turtle char->trans
                   ((char->trans (first string)) state)
                   (rest string))))

(define algae-interp
  (match-lambda
   ['a add1]
   ['b add1]
   [x (lambda (x) x)]))

(define (test-algae n)
  (define (fib n)
    (if (n . <= . 1)
        1
        (+ (fib (- n 1))
           (fib (- n 2)))))
  (test 
   (eval-turtle algae-interp 0 (eval-lsys algae (sub1 n) '(a))) => (fib n)))

(test
 (test-algae 5))
