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

;; GENERAL CODE
(module kernel racket/base
  (require racket/list
           racket/match)

  (provide run-process-until-syscall
           define-syscall
           define-syscalls)

  (define kernel-prompt-tag (make-continuation-prompt-tag 'kernel))
  (define (run-process-until-syscall p)
    (call-with-continuation-barrier
     (λ ()
       (call-with-continuation-prompt
        (λ ()
          (p)
          (error 'kernel "Process did not run to system call"))
        kernel-prompt-tag
        (λ (x) x)))))
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

  (define-syntax-rule
    (define-syscalls state-args
      [call-spec . body]
      ...)
    (begin
      (define-syscall call-spec state-args
        . body)
      ...)))

;; OS-SPECIFIC CODE
(module an-os racket/base
  (require racket/match
           (submod "." ".." kernel))
  (define (snoc* beginning . end)
    (append beginning end))

  (struct process (pid k) #:transparent)
  (struct os (value processes))

  (define-syscalls (pid current)
    [(swap k new-val)
     (match-define (os old-val processes) current)
     (printf "%:~a: Swapping: ~a -> ~a\n" pid old-val new-val)
     (os new-val
         (snoc* processes
                (process pid (λ () (k old-val)))))]
    [(exit k code)
     (printf "%:~a: Exiting ~v\n" pid code)
     current]
    [(print k string)
     (display string)
     (struct-copy
      os current
      [processes
       (snoc* (os-processes current)
              (process pid k))])]
    [(thread-create k t)
     (define t-pid (gensym 'pid))
     (printf "%:~a: Creating new thread: ~a\n" pid t-pid)
     (struct-copy
      os current
      [processes
       (snoc* (os-processes current)
              (process pid (λ () (k t-pid)))
              (process t-pid t))])])

  (define (boot initial-k)
    (let loop ([st (os 0 (list (process (gensym 'pid) initial-k)))])
      (match st
        [(os val (list))
         (printf "%: OS done: ~a\n" val)]
        [(os val (list* (process pid now) future))
         (printf "%: Running thread: ~a\n" pid)
         (define syscall (run-process-until-syscall now))
         (printf "%:~a: Trapped sys-call: ~v\n" pid syscall)
         (loop (syscall pid (os val future)))])))

  (define (printer i)
    (for ([j (in-range i)])
      (print (format "~a: ~a\n" i j)))
    (exit (swap i)))

  (define (init)
    (for ([i (in-range 10)])
      (print
       (format "created ~a\n"
               (thread-create (λ () (printer i))))))
    (exit (swap -1)))

  (boot init))

(require 'an-os)

;; XXX Show other synchronization techniques
;; XXX Interruptss, run in a thread, sync, return syscall with interrupt
