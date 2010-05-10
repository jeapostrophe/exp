#lang racket
(require tests/eli-tester
         "../df.rkt")

(tests
 (behavior? seconds)
 (behavior? 1) => #f
 
 (event? seconds) => #f
 (event? 1) => #f
 (event? (event))
 
 (signal? seconds)
 (signal? 1) => #f
 (signal? (event))
 
 (value-now seconds) => (current-seconds)
 
 (value-now inexact-milliseconds) => (current-inexact-milliseconds)
 
 ; XXX never-e
 
 (local [(define e (event))]
   (event-send! e 1)
   (event-send! e 2)
   (event-record e))
 =>
 (list 1 2)
 
 ; XXX more
 
 )