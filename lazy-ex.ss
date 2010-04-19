#lang scheme
;(require "lazy.ss")
(require "lazy-marks.ss")

(define-syntax-rule (+^ e ...)
  (promise* (lambda () (+ (force* e) ...))))
(define-syntax-rule (/^ e ...)
  (promise* (lambda () (/ (force* e) ...))))

(with-handlers ([(lambda _ #t)
                 (lambda (x) x)])
  (force* 
   (with-continuation-mark
       'test 0
     (+^ 10 
         (/^ 10 
             (promise*
              (lambda ()
                (raise 
                 (continuation-mark-set->list	
                  (current-continuation-marks)
                  'test)))))))))

(with-handlers ([(lambda _ #t)
                 (lambda (x) x)])
  (with-continuation-mark
      'test 0
    (+ 10 
       (/ 10 
          (raise 
           (continuation-mark-set->list	
            (current-continuation-marks)
            'test))))))

(with-handlers ([(lambda _ #t)
                 (lambda (x) x)])
  (force* 
   (with-continuation-mark
       'test 0
     (+^ 10 
         (/^ 10 
             (promise*
              (lambda ()
                5)))))))

(with-handlers ([(lambda _ #t)
                 (lambda (x) x)])
  (with-continuation-mark
      'test 0
    (+ 10 
       (/ 10 
          5))))