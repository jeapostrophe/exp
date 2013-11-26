#lang racket/base
(require racket/list
         racket/match)

                                        ; ! : num -> num
(define (! n)
  (cond
    [(zero? n)
     4]
    [else
     (define nv (! (sub1 n)))
     (printf "! on ~a subcall return ~a\n" n nv)
     (* n nv)]))

                                        ; !^ : num -> (vector num (listof strs))
(define (!^ n)
  (cond
    [(zero? n)
     (vector 4 empty)]
    [else
     (match-define (vector nv strs) (!^ (sub1 n)))
     (vector (* n nv)
             (cons (format "! on ~a subcall return ~a\n" n nv)
                   strs))]))

                                        ; !M : num -> (Debug num)
(struct Debug (val strs))

;; A -> Debug A
(define (Debug-return v)
  (Debug v empty))

;; (Debug A) (A -> (Debug B)) -> (Debug B)
(define (Debug-bind da f)
  (match-define (Debug a strs-from-da) da)
  (match-define (Debug b strs-from-f) (f a))
  (Debug b (append strs-from-da
                   strs-from-f)))

;; String (-> (Debug A)) -> (Debug A)
(define (Debug-add str after)
  (Debug-bind (Debug #f (list str))
              (λ (_) (after))))

(define (!M n)
  (cond
    [(zero? n)
     (Debug-return 4)]
    [else
     (Debug-bind
      (!M (sub1 n))
      (λ (nv)
        (Debug-add
         (format "! on ~a subcall return ~a\n" n nv)
         (λ ()
           (Debug-return (* n nv))))))]))

(module+ test
  (require rackunit/chk)
  (chk (! 4) (* 4 3 2 1))

  (let ()
    (match-define (vector ans strs) (!^ 4))
    (displayln strs)
    (chk ans (* 4 3 2 1)))

  (let ()
    (match-define (Debug ans strs) (!M 4))
    (displayln strs)
    (chk ans (* 4 3 2 1))))

(define list-return list)
(define (list-bind l f)
  (append-map f l))

(module+ test
  (list-bind (list-bind (list 3 4 5 8)
                        (λ (i) (list (add1 i))))
             (λ (i) (list (add1 i)))))
