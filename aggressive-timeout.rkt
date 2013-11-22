#lang racket/base
(require racket/list)

(define (custodian-managed-list* cust super)
  (define ms (custodian-managed-list cust super))
  (append-map
   (λ (v)
     (if (custodian? v)
       (custodian-managed-list* v cust)
       (list v)))
   ms))

(define (aggressive-timeout secs code)
  (define me
    (current-custodian))
  (define cust
    (make-custodian me))
  (define timeout-evt
    (handle-evt
     (alarm-evt (+ (current-inexact-milliseconds)
                   (* 1000 secs)))
     (λ (a)
       (custodian-shutdown-all cust)
       (error 'aggressive-timeout "code used too many secs"))))

  (parameterize ([current-custodian cust])
    (thread code))

  (let loop ()
    (define ms (custodian-managed-list* cust me))
    (define ts (filter thread? ms))
    (sync
     (if (empty? ts)
       always-evt
       (handle-evt
        (apply choice-evt (map thread-dead-evt ts))
        (λ _
          (loop))))
     timeout-evt)))

(module+ test
  (require rackunit/chk)
  (define n 1)
  (chk
   #:t
   (aggressive-timeout
    n
    (λ () (sleep (sub1 n))))

   #:exn
   (aggressive-timeout
    n
    (λ () (sleep (add1 n))))
   exn:fail?

   #:exn
   (aggressive-timeout
    n
    (λ ()
      (thread (λ () (sleep (add1 n))))))
   exn:fail?

   #:exn
   (aggressive-timeout
    n
    (λ ()
      (thread (λ ()
                (thread (λ () (sleep (add1 n))))))))
   exn:fail?

   #:exn
   (aggressive-timeout
    n
    (λ ()
      (parameterize ([current-custodian (make-custodian)])
        (thread (λ () (sleep (add1 n)))))))
   exn:fail?))
