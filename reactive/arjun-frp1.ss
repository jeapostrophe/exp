#lang scheme
(require scheme/gui)

(define reactive-prompt (make-continuation-prompt-tag 'reactive))

(define-syntax sink 
  (syntax-rules ()
    [(_ code v ...) (code (lambda () v) ...)]))

(define-syntax sink-lambda
  (syntax-rules ()
      [(_ (arg ...) body ...)
       (lambda (arg ...)
         (call-with-continuation-prompt
          (lambda () body ...)
          reactive-prompt))]))
     
(define (timer interval)
  (call-with-composable-continuation
   (lambda (k)
     (new timer% 
            [notify-callback 
             (lambda () (k (quotient (current-milliseconds) 1000)))]
            [interval (* interval 1000)]
            [just-once? #f]))
   reactive-prompt)
  (quotient (current-milliseconds) 1000))

(define observe
  (sink-lambda (comment value)
    (let* ([frame (new frame% [label "Current Value"] [height 80] [width 300])]
           [msg (new message% [parent frame] [label ""] [min-width 300])])
      (send frame show #t)
      (send msg set-label (format "~a: ~a" (comment) (value))))))

(call-with-continuation-prompt
 (lambda ()

   (sink observe 
         "should be true" 
         (let ([t (timer 1)])
           (< t (+ t 1))))
   
   (sink observe
         "Now"
         (timer 1))

   (sink observe
         "Should be false"
         (let ([t (timer 1)])
           (>= t (+ t 1))))
   
   (sink observe
         "No errors"
         (let ([t (timer 1)])
           (if (even? t)
               "NO DIVISION"
               (/ 1 (modulo t 2)))))
   
   )
 reactive-prompt)