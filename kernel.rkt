#lang racket/base
(require racket/list
         racket/match)

(define (snoc* beginning . end)
  (append beginning end))

;; This shows the basic structure of an OS kernel.

;; Processes get to run, they have system calls that access special
;; resources---in this case STDOUT and creating new processes. You
;; could adapt this pretty easily to use a sensible scheduling
;; algorithm a la priority queue; add more system calls; provide
;; event-based waiting facilities, rather than just blocking
;; primitives; etc.

;; It would be nice to have a cleaner way of writing the system call
;; handlers, without using global mutation. Perhaps you'd reify the
;; kernel state in a structure and have the system call handlers be
;; State -> State functions and then you'd define a macro to add them
;; to a dispatch table and create a user wrapper. 

;; I wonder if it would be fun/reasonable to design an OS class around
;; building a kernel like this. You'd combine it with some stuff like
;; the GC language to control what the student was allowed to do in
;; the user programs.
(define kernel-prompt-tag (make-continuation-prompt-tag))
(define (boot initial-process)
  (let loop ([ts (list initial-process)])
    (match ts
      [(list)
       (printf "%: OS is done\n")]
      [(list* now future)
       (printf "%: Running thread: ~v\n" now)
       (call-with-continuation-prompt
        (λ ()
          (now)
          (error '% "Process run to completion without syscall: ~v" now))
        kernel-prompt-tag
        (λ (k call-sym args)
          (match* (call-sym args)
            [('exit (list code))
             (printf "%:~v: Exiting ~v\n" now code)
             (loop future)]
            [('print (list string))
             (display string)
             (loop (snoc* future k))]
            [('thread-create (list t))
             (printf "%:~a: Creating new thread: ~v\n" now t)
             (loop (snoc* future k t))])))])))
(define (syscall call-sym . args)
  ;; First we capture our context back to the OS
  (call-with-current-continuation
   (λ (k)
     ;; Then we abort, give it to the OS, along with a syscall
     ;; specification
     (abort-current-continuation
      kernel-prompt-tag
      k call-sym args))
   kernel-prompt-tag))

(define (printer i)
  (for ([j (in-range i)])
    (syscall 'print (format "~a: ~a\n" i j)))
  (syscall 'exit 0))

(define (init)
  (for ([i (in-range 10)])
    (syscall 'thread-create (λ () (printer i))))
  (syscall 'exit 0))

(boot init)
