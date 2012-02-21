#lang racket/base
(require racket/list
         racket/unsafe/ops
         racket/match)

;; Problem: Find the k-th element from the end of a list.

(define (reverse&list-ref k l)
  (list-ref (reverse l) k))

(define (unsafe-reverse&list-ref k l)
  (unsafe-list-ref (reverse l) k))

(define (length&list-ref k l)
  (list-ref l (- (length l) k 1)))

(define (unsafe-length&list-ref k l)
  (unsafe-list-ref l (unsafe-fx- (length l) (unsafe-fx+ k 1))))

(define (double-walk k l)
  (let loop ([l l]
             [k-down
              (list-tail l (+ k 1))])
    (if (empty? k-down)
        (first l)
        (loop (rest l)
              (rest k-down)))))

(define (unsafe-double-walk k l)
  (let loop ([l l]
             [k-down
              (unsafe-list-tail l (unsafe-fx+ k 1))])
    (if (null? k-down)
        (unsafe-car l)
        (loop (unsafe-cdr l)
              (unsafe-cdr k-down)))))

(define (fuse-length+list-ref k l)
  (let/ec
   esc
   (let loop ([l l])
     (if (empty? l)
         0
         (let ()
           (define n (loop (rest l)))
           (if (= n k)
               (esc (first l))
               (add1 n)))))))

(define (unsafe-fuse-length+list-ref k l)
  (let/ec
   esc
   (let loop ([l l])
     (if (null? l)
         0
         (let ()
           (define n (loop (unsafe-cdr l)))
           (if (= n k)
               (esc (unsafe-car l))
               (unsafe-fx+ n 1)))))))

(define (ring-buffer k+ l)
  (define next 0)
  (define k (add1 k+))
  (define rb (make-vector k #f))
  (let loop ([l l])
    (if (empty? l)
        (vector-ref rb (modulo (- next k) k))
        (begin (vector-set! rb next (first l))
               (set! next (modulo (add1 next) k))
               (loop (rest l))))))

(define (unsafe-ring-buffer k+ l)
  (define next 0)
  (define k (unsafe-fx+ k+ 1))
  (define rb (make-vector k #f))
  (let loop ([l l])
    (if (null? l)
        (unsafe-vector-ref rb (unsafe-fxmodulo (unsafe-fx- next k) k))
        (begin (unsafe-vector-set! rb next (unsafe-car l))
               (set! next (unsafe-fxmodulo (unsafe-fx+ next 1) k))
               (loop (unsafe-cdr l))))))

(require rackunit)
(define (test-it list-size k%)
  (define l (build-list list-size (λ (i) (- list-size i 1))))
  (define k (random (inexact->exact (round (* k% list-size)))))
  (printf "\n\nList is ~a long, k is ~a\n" list-size k)
  (λ (label f)
     (test-equal? (symbol->string label)
                  (f k l)
                  k)))

(require tests/stress)
(define-syntax-rule (stress* make-test-it n id ...)
  (let ()
    (define test-it make-test-it)
    (stress n ['id (test-it 'id id)] ...)))

(define-syntax-rule (stress**  l k%)
  (stress* (test-it l k%) 10
           unsafe-reverse&list-ref
           unsafe-length&list-ref
           reverse&list-ref
           length&list-ref
           double-walk unsafe-double-walk
           fuse-length+list-ref unsafe-fuse-length+list-ref
           ring-buffer unsafe-ring-buffer))

(stress** 1000000 .001)
(stress** 1000000 .01)
(stress** 1000000 .1)
(stress** 1000000 .9)

#<<END
-*- mode: compilation; default-directory: "/home/jay/Dev/scm/github.jeapostrophe/" -*-
Compilation started at Tue Feb 21 10:34:12

zsh -i -c 'rk "/home/jay/Dev/scm/github.jeapostrophe/k-from-end.rkt"'


List is 1000000 long, k is 589
unsafe-double-walk: cpu: 9.600000000000001 real: 9.999999999999998 gc: 0.0 (averaged over 10 runs)
length&list-ref: cpu: 17.6 real: 17.7 gc: 0.0 (averaged over 10 runs)
unsafe-length&list-ref: cpu: 18.4 real: 17.599999999999998 gc: 0.0 (averaged over 10 runs)
unsafe-ring-buffer: cpu: 30.0 real: 29.4 gc: 0.0 (averaged over 10 runs)
double-walk: cpu: 56.0 real: 55.3 gc: 0.0 (averaged over 10 runs)
ring-buffer: cpu: 69.6 real: 68.89999999999999 gc: 0.0 (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 76.80000000000001 real: 76.89999999999999 gc: 30.000000000000007 (averaged over 10 runs)
fuse-length+list-ref: cpu: 134.4 real: 132.79999999999998 gc: 13.200000000000001 (averaged over 10 runs)
reverse&list-ref: cpu: 142.0 real: 142.1 gc: 118.4 (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 158.4 real: 159.3 gc: 129.6 (averaged over 10 runs)
Normalized:
unsafe-double-walk: cpu: 1.00 real: 1.00 gc: inf (averaged over 10 runs)
length&list-ref: cpu: 1.83 real: 1.77 gc: inf (averaged over 10 runs)
unsafe-length&list-ref: cpu: 1.92 real: 1.76 gc: inf (averaged over 10 runs)
unsafe-ring-buffer: cpu: 3.12 real: 2.94 gc: inf (averaged over 10 runs)
double-walk: cpu: 5.83 real: 5.53 gc: inf (averaged over 10 runs)
ring-buffer: cpu: 7.25 real: 6.89 gc: inf (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 8.00 real: 7.69 gc: inf (averaged over 10 runs)
fuse-length+list-ref: cpu: 14.00 real: 13.28 gc: inf (averaged over 10 runs)
reverse&list-ref: cpu: 14.79 real: 14.21 gc: inf (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 16.50 real: 15.93 gc: inf (averaged over 10 runs)



List is 1000000 long, k is 2587
unsafe-double-walk: cpu: 10.0 real: 10.0 gc: 0.0 (averaged over 10 runs)
unsafe-length&list-ref: cpu: 17.599999999999998 real: 17.6 gc: 0.0 (averaged over 10 runs)
length&list-ref: cpu: 18.000000000000004 real: 18.299999999999997 gc: 0.0 (averaged over 10 runs)
unsafe-ring-buffer: cpu: 33.2 real: 34.0 gc: 0.0 (averaged over 10 runs)
double-walk: cpu: 55.199999999999996 real: 54.70000000000001 gc: 0.0 (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 71.6 real: 71.6 gc: 15.2 (averaged over 10 runs)
ring-buffer: cpu: 81.60000000000001 real: 82.49999999999999 gc: 0.0 (averaged over 10 runs)
fuse-length+list-ref: cpu: 142.4 real: 144.10000000000002 gc: 13.200000000000001 (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 147.6 real: 148.4 gc: 123.2 (averaged over 10 runs)
reverse&list-ref: cpu: 171.70000000000002 real: 176.0 gc: 143.3 (averaged over 10 runs)
Normalized:
unsafe-double-walk: cpu: 1.00 real: 1.00 gc: inf (averaged over 10 runs)
unsafe-length&list-ref: cpu: 1.76 real: 1.76 gc: inf (averaged over 10 runs)
length&list-ref: cpu: 1.80 real: 1.83 gc: inf (averaged over 10 runs)
unsafe-ring-buffer: cpu: 3.32 real: 3.40 gc: inf (averaged over 10 runs)
double-walk: cpu: 5.52 real: 5.47 gc: inf (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 7.16 real: 7.16 gc: inf (averaged over 10 runs)
ring-buffer: cpu: 8.16 real: 8.25 gc: inf (averaged over 10 runs)
fuse-length+list-ref: cpu: 14.24 real: 14.41 gc: inf (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 14.76 real: 14.84 gc: inf (averaged over 10 runs)
reverse&list-ref: cpu: 17.17 real: 17.60 gc: inf (averaged over 10 runs)



List is 1000000 long, k is 99627
unsafe-double-walk: cpu: 14.799999999999999 real: 14.900000000000002 gc: 0.0 (averaged over 10 runs)
unsafe-length&list-ref: cpu: 18.0 real: 17.7 gc: 0.0 (averaged over 10 runs)
length&list-ref: cpu: 19.200000000000003 real: 19.1 gc: 0.0 (averaged over 10 runs)
unsafe-ring-buffer: cpu: 36.8 real: 37.6 gc: 0.0 (averaged over 10 runs)
double-walk: cpu: 63.599999999999994 real: 63.6 gc: 0.0 (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 72.8 real: 73.5 gc: 18.0 (averaged over 10 runs)
ring-buffer: cpu: 81.6 real: 82.0 gc: 0.0 (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 149.20000000000002 real: 149.5 gc: 123.6 (averaged over 10 runs)
fuse-length+list-ref: cpu: 161.6 real: 163.29999999999998 gc: 20.799999999999997 (averaged over 10 runs)
reverse&list-ref: cpu: 162.80000000000004 real: 163.39999999999998 gc: 135.2 (averaged over 10 runs)
Normalized:
unsafe-double-walk: cpu: 1.00 real: 1.00 gc: inf (averaged over 10 runs)
unsafe-length&list-ref: cpu: 1.22 real: 1.19 gc: inf (averaged over 10 runs)
length&list-ref: cpu: 1.30 real: 1.28 gc: inf (averaged over 10 runs)
unsafe-ring-buffer: cpu: 2.49 real: 2.52 gc: inf (averaged over 10 runs)
double-walk: cpu: 4.30 real: 4.27 gc: inf (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 4.92 real: 4.93 gc: inf (averaged over 10 runs)
ring-buffer: cpu: 5.51 real: 5.50 gc: inf (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 10.08 real: 10.03 gc: inf (averaged over 10 runs)
fuse-length+list-ref: cpu: 10.92 real: 10.96 gc: inf (averaged over 10 runs)
reverse&list-ref: cpu: 11.00 real: 10.97 gc: inf (averaged over 10 runs)



List is 1000000 long, k is 367152
length&list-ref: cpu: 16.0 real: 16.099999999999998 gc: 0.0 (averaged over 10 runs)
unsafe-length&list-ref: cpu: 16.8 real: 17.0 gc: 0.0 (averaged over 10 runs)
unsafe-double-walk: cpu: 18.0 real: 17.600000000000005 gc: 0.0 (averaged over 10 runs)
unsafe-ring-buffer: cpu: 35.2 real: 35.89999999999999 gc: 0.0 (averaged over 10 runs)
double-walk: cpu: 54.4 real: 55.699999999999996 gc: 0.0 (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 74.8 real: 75.4 gc: 16.8 (averaged over 10 runs)
ring-buffer: cpu: 78.4 real: 77.80000000000001 gc: 0.0 (averaged over 10 runs)
fuse-length+list-ref: cpu: 167.7 real: 168.5 gc: 22.400000000000002 (averaged over 10 runs)
reverse&list-ref: cpu: 176.0 real: 177.8 gc: 144.4 (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 182.4 real: 184.50000000000003 gc: 148.4 (averaged over 10 runs)
Normalized:
length&list-ref: cpu: 1.00 real: 1.00 gc: inf (averaged over 10 runs)
unsafe-length&list-ref: cpu: 1.05 real: 1.06 gc: inf (averaged over 10 runs)
unsafe-double-walk: cpu: 1.12 real: 1.09 gc: inf (averaged over 10 runs)
unsafe-ring-buffer: cpu: 2.20 real: 2.23 gc: inf (averaged over 10 runs)
double-walk: cpu: 3.40 real: 3.46 gc: inf (averaged over 10 runs)
unsafe-fuse-length+list-ref: cpu: 4.67 real: 4.68 gc: inf (averaged over 10 runs)
ring-buffer: cpu: 4.90 real: 4.83 gc: inf (averaged over 10 runs)
fuse-length+list-ref: cpu: 10.48 real: 10.47 gc: inf (averaged over 10 runs)
reverse&list-ref: cpu: 11.00 real: 11.04 gc: inf (averaged over 10 runs)
unsafe-reverse&list-ref: cpu: 11.40 real: 11.46 gc: inf (averaged over 10 runs)


Compilation finished at Tue Feb 21 10:35:06
END
