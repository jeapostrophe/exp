#lang racket/base

(define (kill-unless-sema-after-secs t sema secs)
  (thread
   (λ ()
     (sync sema
           (handle-evt (alarm-evt (+ (current-inexact-milliseconds)
                                     (* 1000 secs)))
                       (λ _
                         (kill-thread t)))))))

(module+ main
  (define t
    (thread
     (thunk
       (let loop ()
         (define sema (make-semaphore))
         (kill-unless-sema-after-secs t sema secs)
         (define-values (len shost sport)
           (udp-receive! socket buffer))
         (semaphore-post sema)
         ;; xxx do stuff
         (loop))))))
