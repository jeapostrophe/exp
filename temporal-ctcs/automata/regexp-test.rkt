#lang racket
(require "regexp.rkt"
         "regexp-ext.rkt"
         tests/eli-tester)

(define-syntax-rule (test-regex* R (succ ...) (fail ...))
  (let ()
    (define r (regex R))
    (test #:failure-prefix (format "~s" 'R)
          (test
           (regex-accepts? r succ) ...
           (not (regex-accepts? r fail)) ...))))
(define-syntax-rule (test-regex R (succ ...) (fail ...))
  (test (test-regex* R (succ ...) (fail ...))
        #;(test-regex* (complement R) (fail ...) (succ ...))))

(test
 (test-regex "A"
             [(list "A")]
             [(list)
              (list "B")])
 
 #;(test-regex (complement "A")
             [(list)
              (list "B")
              (list "A" "A")]
             [(list "A")])
 
 (test-regex (seq 0 1)
             [(list 0 1)]
             [(list)
              (list 0)
              (list 0 1 1)])
 
 (test-regex (union 0 1)
             [(list 1)
              (list 0)]
             [(list)
              (list 0 1)
              (list 0 1 1)])
 
 (test-regex (star 0)
             [(list)
              (list 0)
              (list 0 0)]
             [(list 1)])
 
 (test-regex epsilon
             [(list)]
             [(list 0)])
 
 (test-regex (opt "A")
             [(list)
              (list "A")]
             [(list "B")])

 (test-regex (plus "A")
             [(list "A")
              (list "A" "A")]
             [(list)])
 
 (test-regex (rep "A" 3)
             [(list "A" "A" "A")]
             [(list)
              (list "A")
              (list "A" "A")])
 
 (test-regex never
             []
             [(list) (list 1)])
 
 #;(test-regex (difference (? even?) 2)
             [(list 4)
              (list 6)]
             [(list 3)
              (list 2)])
 
 #;(test-regex (intersection (? even?) 2)
             [(list 2)]
             [(list 1)
              (list 4)])
 
 #;(test-regex (complement (seq "A" (opt "B")))
             [(list "A" "B" "C")]
             [(list "A")
              (list "A" "B")])
 
 (test-regex (seq epsilon
              (union (seq (star 1) (star (seq 0 (star 1) 0 (star 1))))
                     (seq (star 0) (star (seq 1 (star 0) 1 (star 0)))))
              epsilon)
             [(list 1 0 1 0 1)
              (list 0 1 0 1 0)
              (list 1 0 1 1 0 1)
              (list 0 1 0 0 1 0)
              (list)]
             [(list 1 0)]))