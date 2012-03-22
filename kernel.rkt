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

  (define (go)
    (boot init))
  (provide go))

(printf "Kernel based\n")
(require (prefix-in kernel: 'an-os))
(kernel:go)

(module locking racket/base
  (require (prefix-in racket: racket/base)
           racket/match
           racket/list)

  (define os-lock (make-semaphore 1))
  (define os-value 0)
  (define threads empty)

  (define (swap new-val)
    (call-with-semaphore
     os-lock
     (λ ()
       (define old-val os-value)
       (printf "%:~a: Swapping: ~a -> ~a\n" (current-thread) old-val new-val)
       (set! os-value new-val)
       old-val)))

  (define (exit code)
    (call-with-semaphore
     os-lock
     (λ ()
       (printf "%:~a: Exiting ~v\n" (current-thread) code)
       (set! threads (remq (current-thread) threads)))))

  (define (print string)
    (call-with-semaphore
     os-lock
     (λ ()
       (display string))))

  (define (thread-create t)
    (call-with-semaphore
     os-lock
     (λ ()
       (define t-pid (thread t))
       (set! threads (list* t-pid threads))
       (printf "%:~a: Creating new thread: ~a\n" (current-thread) t-pid)
       t-pid)))

  (define (boot initial-k)
    (call-with-semaphore
     os-lock
     (λ ()
       (define init-t
         (thread initial-k))
       (set! threads (list init-t))))
    (let loop ()
      (match
          (call-with-semaphore
           os-lock
           (λ () threads))
        [(list)
         os-value]
        [_
         (sleep)
         (loop)])))

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

  (define (go)
    (boot init))
  (provide go))

(printf "Locking based\n")
(require (prefix-in locking: 'locking))
(locking:go)

(module messaging racket/base
  (require (prefix-in racket: racket/base)
           racket/match
           racket/list)

  (define message-ch (make-channel))

  (define-syntax-rule
    (define-syscall (call-struct call field ...))
    (begin
      (struct call-struct (ct reply-ch field ...))
      (define (call field ...)
        (define reply-ch (make-channel))
        (channel-put message-ch
                     (call-struct (current-thread) reply-ch field ...))
        (channel-get reply-ch))))
  (define-syntax-rule
    (define-syscalls call ...)
    (begin (define-syscall call) ...))

  (define-syscalls
    (swap* swap new-val)
    (exit* exit code)
    (print* print string)
    (thread-create* thread-create t))

  (define (boot initial-k)
    (let loop ([value 0]
               [threads (list (thread initial-k))])
      (if (empty? threads)
        value
        (match (sync message-ch)
          [(swap* ct reply-ch new-val)
           (define old-val value)
           (printf "%:~a: Swapping: ~a -> ~a\n" ct old-val new-val)
           (channel-put reply-ch old-val)
           (loop new-val threads)]
          [(exit* ct reply-ch code)
           (printf "%:~a: Exiting ~v\n" ct code)
           (channel-put reply-ch (void))
           (loop value (remq ct threads))]
          [(print* t reply-ch string)
           (display string)
           (channel-put reply-ch (void))
           (loop value threads)]
          [(thread-create* ct reply-ch t)
           (define t-pid (thread t))
           (printf "%:~a: Creating new thread: ~a\n" ct t-pid)
           (channel-put reply-ch t-pid)
           (loop value (list* t-pid threads))]))))

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

  (define (go)
    (boot init))
  (provide go))

(printf "Messaging based\n")
(require (prefix-in messaging: 'messaging))
(messaging:go)

;; XXX Interruptss, run in a thread, sync, return syscall with interrupt
