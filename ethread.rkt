#lang racket

#|

Threads with exit status

|#
(require racket/async-channel)

(struct *thread* (real-thread exit-ch exit-status-box) #:mutable)
(struct thread-ans ())
(struct thread-ans:exn thread-ans (x))
(struct thread-ans:val thread-ans (x))

(define (new-thread thnk)
  (define t
    (thread
     (lambda ()
       (with-handlers
           ([void
             (lambda (x)
               (async-channel-put ch (thread-ans:exn x)))])
         (async-channel-put ch (thread-ans:val (thnk)))))))
  (define ch (make-async-channel 1))
  (*thread* t ch (box #f)))

(define (update-thread! thd)
  (match-define (*thread* t ch stb) thd)
  (cond
   ;; It is dead, but we haven't got the answer
   [(and (thread-dead? t) ch)
    ;; Get the value
    (set-box! stb (async-channel-get ch))
    ;; Destroy the channel
    (set-*thread*-exit-ch! thd #f)]
   ;; It is dead, we have got the answer
   [(and (thread-dead? t) (not ch))
    (void)]
   ;; It is not dead, so keep running
   [(not (thread-dead? t))
    (void)])
  thd)

(define (thread-died-with-exception? thd)
  (match-define (*thread* t ch stb) (update-thread! thd))
  (cond
   [(not (thread-dead? t))
    (error 'hasnt-died-yet)]
   [(thread-ans:exn? (unbox stb))
    #t]
   [(thread-ans:val? (unbox stb))
    #f]))

(define (thread-exception thd)
  (match-define (*thread* t ch stb) (update-thread! thd))
  (cond
   [(not (thread-dead? t))
    (error 'hasnt-died-yet)]
   [(thread-ans:exn? (unbox stb))
    (thread-ans:exn-x (unbox stb))]
   [(thread-ans:val? (unbox stb))
    (error 'didnt-raise)]))

(define (thread-result thd)
  (match-define (*thread* t ch stb) (update-thread! thd))
  (cond
   [(not (thread-dead? t))
    (error 'hasnt-died-yet)]
   [(thread-ans:exn? (unbox stb))
    (error 'raised)]
   [(thread-ans:val? (unbox stb))
    (thread-ans:val-x (unbox stb))]))

(define (*thread*-wait thd)
  (match-define (*thread* t ch stb) thd)
  (thread-wait t))

(require tests/eli-tester)

(test
 (let ()
   (define t (new-thread (lambda () (semaphore-wait (make-semaphore)))))
   (test (thread-died-with-exception? t) => (error 'hasnt-died-yet)
         (thread-exception t) => (error 'hasnt-died-yet)
         (thread-result t) => (error 'hasnt-died-yet)))
 (let ()
   (define t (new-thread (lambda () (raise 1))))
   (test (*thread*-wait t) => (void)
         (thread-died-with-exception? t) => #t
         (thread-exception t) => 1
         (thread-result t) => (error 'raised)))
 (let ()
   (define t (new-thread (lambda () 1)))
   (test (*thread*-wait t) => (void)
         (thread-died-with-exception? t) => #f
         (thread-exception t) => (error 'didnt-raise)
         (thread-result t) => 1)))
