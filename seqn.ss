#lang scheme
(require tests/eli-tester)

(define (in-list* l n)
  (make-do-sequence
   (lambda ()
     (values (lambda (l) (apply values (take l n)))
             (lambda (l) (drop l n))
             l
             (lambda (l) (>= (length l) n))
             (lambda _ #t)
             (lambda _ #t)))))

(define l (list 1 2 3 4))

(test
 (for/list ([i (in-list l)]) i) => '(1 2 3 4)
 (for/list ([i (in-list* l 1)]) i) => '(1 2 3 4)
 (for/list ([(i j) (in-list* l 2)]) (cons i j)) => '((1 . 2) (3 . 4))
 (for/list ([(i j k) (in-list* l 3)]) (list i j k)) => '((1 2 3))) 

(define (in-vector* v n)
  (make-do-sequence
   (λ ()
     (values (λ (i) (vector->values v i (+ i n)))
             (λ (i) (+ i n))
             0
             (λ (i) (>= (vector-length v) (+ i n)))
             (λ _ #t)
             (λ _ #t)))))

(define v (vector 1 2 3 4))

(test
 (for/list ([i (in-vector v)]) i) => '(1 2 3 4)
 (for/list ([i (in-vector* v 1)]) i) => '(1 2 3 4)
 (for/list ([(i j) (in-vector* v 2)]) (cons i j)) => '((1 . 2) (3 . 4))
 (for/list ([(i j k) (in-vector* v 3)]) (list i j k)) => '((1 2 3)))