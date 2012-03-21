;; This shows the basic structure of an OS kernel.

;; Processes get to run, they have system calls that access special
;; resources---in this case STDOUT and creating new processes. You
;; could adapt this pretty easily to use a sensible scheduling
;; algorithm a la priority queue; add more system calls; provide
;; event-based waiting facilities, rather than just blocking
;; primitives; etc.

;; I wonder if it would be fun/reasonable to design an OS class around
;; building a kernel like this. You'd combine it with some stuff like
;; the GC language to control what the student was allowed to do in
;; the user programs.
#lang racket/base
(require racket/list
         racket/match)

;; GENERAL CODE
(define kernel-prompt-tag (make-continuation-prompt-tag 'kernel))
(define (run-process-until-syscall p)
  (call-with-continuation-barrier
   (λ ()
     (call-with-continuation-prompt p kernel-prompt-tag (λ (x) x)))))
(define (trap-syscall k->syscall)
  ;; First we capture our context back to the OS
  (call-with-current-continuation
   (λ (k)
     ;; Then we abort, give it to the OS, along with a syscall
     ;; specification
     (abort-current-continuation kernel-prompt-tag (k->syscall k)))
   kernel-prompt-tag))

(define-syntax-rule
  (define-syscall (call k call-arg ...) state-args
    body ...)
  (define call
    (let ()
      (struct call (k call-arg ...)
              #:property prop:procedure
              (λ (the-struct . state-args)
                (match-define (call k call-arg ...) the-struct)
                body ...)
              #:transparent)
      (λ (call-arg ...)
        (trap-syscall
         (λ (k)
           (call k call-arg ...)))))))

;; OS-SPECIFIC CODE
(define (snoc* beginning . end)
  (append beginning end))

(struct process (pid k) #:transparent)

(define-syscall (exit k code) (pid future)
  (printf "%:~a: Exiting ~v\n" pid code)
  future)
(define-syscall (print k string) (pid future)
  (display string)
  (snoc* future (process pid k)))
(define-syscall (thread-create k t) (pid future)
  (define t-pid (gensym 'pid))
  (printf "%:~a: Creating new thread: ~a\n" pid t-pid)
  (snoc* future
         (process pid (λ () (k t-pid)))
         (process t-pid t)))

(define (boot initial-k)
  (let loop ([ts (list (process (gensym 'pid) initial-k))])
    (match ts
      [(list)
       (printf "%: OS is done\n")]
      [(list* (process pid now) future)
       (printf "%: Running thread: ~a\n" pid)
       (define syscall (run-process-until-syscall now))
       (printf "%:~a: Trapped sys-call: ~v\n" pid syscall)
       (loop (syscall pid future))])))

(define (printer i)
  (for ([j (in-range i)])
    (print (format "~a: ~a\n" i j)))
  (exit 0))

(define (init)
  (for ([i (in-range 10)])
    (print
     (format "created ~a\n"
             (thread-create (λ () (printer i))))))
  (exit 0))

(boot init)
