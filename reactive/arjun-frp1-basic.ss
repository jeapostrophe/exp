#lang scheme
(require scheme/gui)

(define reactive-prompt (make-continuation-prompt-tag 'reactive))

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

(define (observe comment return-behavior)
  ; Without this prompt, the system will repeatedly create observers.
  (call-with-continuation-prompt
   (lambda ()
     (let* ([frame (new frame% [label "Current Value"] [height 80] [width 300])]
            [msg (new message% [parent frame] [label ""] [min-width 300])])
       (send frame show #t)
       (send msg set-label (format "~a: ~a" comment (return-behavior)))))
   reactive-prompt))


(call-with-continuation-prompt
 (lambda ()

   (observe 
    "should be true" 
    (lambda ()
      (let ([t (timer 1)])
        (< t (+ t 1)))))
   
   (observe
    "Now"
    (lambda () (timer 1)))

   (observe
    "Should be false"
    (lambda ()
      (let ([t (timer 1)])
        (>= t (+ t 1)))))
   
   (observe
    "No errors"
    (lambda ()
      (let ([t (timer 1)])
        (if (even? t)
            "NO DIVISION"
            (/ 1 (modulo t 2))))))
   
   (observe
    "#t/#f"
    (lambda () (even? (timer 1))))
   
   (observe 
    "even and odd?!"
    (lambda () 
      (let ([t (timer 1)])
        (and (even? t) (odd? t)))))
   
   )
 reactive-prompt)