#lang scheme
(require tests/eli-tester)

(define-syntax-rule (my-let/cc k e ...)
  (call-with-current-continuation
   (lambda (k) e ...)))

(define marker1 (make-continuation-prompt-tag 'marker1))
(define marker2 (make-continuation-prompt-tag 'marker2))

(test
 (+ 1 
    (let/cc k
      (+ 5
         (k 3))))
 =>
 4
 
 (+ 1 
    3)
 =>
 4
 
 (+ 1 
    (my-let/cc k
               (+ 5
                  (k 3))))
 =>
 4
 
 (+ 1 
    (call-with-current-continuation
     (lambda (k)
       (+ 5
          (k 3)))))
 =>
 4
 
 (call-with-continuation-prompt
  (lambda ()
    (+ 1 
       (call-with-composable-continuation
        (lambda (k)
          (+ 5
             (k 3)))))))
 =>
 10
 
 (call-with-continuation-prompt
  (lambda ()
    (+ 1 
       (call-with-composable-continuation
        (lambda (k)
          (+ 5
             (k 3)))
        marker1)))
  marker1)
 =>
 10
 
 (call-with-continuation-prompt
  (lambda ()
    (+ 1 
       (call-with-composable-continuation
        (lambda (k)
          (+ 5
             (k 3)))
        marker2)))
  marker1)
 =error>
 "marker2"
 
 (call-with-continuation-prompt
  (lambda ()
    (+ 1 
       (call-with-continuation-prompt
        (lambda ()
          (+ 2 
             (call-with-composable-continuation
              (lambda (k)
                (+ 5
                   (k 3)))
              marker2)))
        marker2)))
  marker1)
 =>
 13
 
 (call-with-continuation-prompt
  (lambda ()
    (+ 1 
       (call-with-continuation-prompt
        (lambda ()
          (+ 2 
             (call-with-composable-continuation
              (lambda (k)
                (+ 5
                   (k 3)))
              marker1)))
        marker2)))
  marker1)
 =>
 14
 
 )

;; Zipper
(define zipper-prompt
  (make-continuation-prompt-tag 'zipper))
(define (zipper-in p l)
  (define (walk esc p l)
    (match p
      [(list)
       (call-with-composable-continuation
        (lambda (k) (esc k))
        zipper-prompt)]
      [(list-rest 'car p)
       (cons (walk esc p (car l))
             (cdr l))]
      [(list-rest 'cdr p)
       (cons (car l)
             (walk esc p (cdr l)))]))
  (let/cc esc
    (call-with-continuation-prompt
     (lambda ()
       (walk esc p l))
     zipper-prompt)))

(test
 
 ((zipper-in '(car) (list 1)) 5) => (list 5)
 ((zipper-in '(car car car cdr) (list (list (list (list 1))))) 7) =>
 (list (list (list (cons 1 7))))

 ((zipper-in '(cdr cdr car) (list 1 2 3 4)) 7) => (list 1 2 7 4)

 ((zipper-in '(cdr) (list 1 2 3 4)) (list 5 6 7)) => (list 1 5 6 7)
 
 )


;; How the web server uses

#|
;; Dynamic
"X1"
(dynamic-wind
 (lambda ()
   (printf "Pre~n"))
 (lambda ()
   (printf "In~n"))
 (lambda ()
   (printf "Out~n")))

"X2"
#;(dynamic-wind
 (lambda ()
   (printf "Pre~n"))
 (lambda ()
   (error 'x))
 (lambda ()
   (printf "Out~n")))

"X3"
(define k #f)
(dynamic-wind
 (lambda ()
   (printf "Pre~n"))
 (lambda ()
   (define ans 5)
   (printf "In~n")
   (let/cc in-k
     (unless k
       (set! k in-k))     
     (set! ans 6))
   ans)
 (lambda ()
   (printf "Out~n")))
(k 'null)

|#