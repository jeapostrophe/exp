#lang racket/base
(for ([n (in-range 1 101)])
  (displayln
   (case (gcd n 15)
     [(15) "FizzBuzz"]
     [(3) "Fizz"]
     [(5) "Buzz"]
     [else n])))
