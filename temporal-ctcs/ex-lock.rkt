#lang racket/load

#| This file is an attempt to show a different style of monitor
   that doesn't record the event trace, but rather records the
   pertinent information.
|#

(module lock racket
  (require "temporal.rkt" unstable/match)
  (define (use-resource f)
    (f (λ () "lock" (void))
       (λ () "use" (void))
       (λ () "unlock" (void))))  
  
  (define locked? (make-weak-hasheq))
  (define lock->user (make-weak-hasheq))
  (define unlock->user (make-weak-hasheq))
  (define use->user (make-weak-hasheq))
  (define returned? (make-weak-hasheq))
  (define (monitor evt)
    (let/ec esc
      (define (fail) (esc #f))
      (match evt
        [(evt:call 'user _ _ _ _ app (list lock use unlock))
         (hash-set! lock->user (projection-label lock) app)
         (hash-set! use->user (projection-label use) app)
         (hash-set! unlock->user (projection-label unlock) app)]
        [(evt:return 'user _ _ _ _ app _ _)
         (hash-set! returned? app #t)]
        [(evt:return 'lock p _ _ _ _ _ _)
         (hash-set! locked? (hash-ref lock->user p fail) #t)]
        [(evt:return 'unlock p _ _ _ _ _ _)
         (hash-set! locked? (hash-ref unlock->user p fail) #f)]
        [_
         (void)])
      (and
       (match evt
        ; Must not lock or unlock twice
        [(evt:call 'lock p _ _ _ _ _)
         (not (hash-ref locked? (hash-ref lock->user p fail) #f))]
        [(evt:call 'unlock p _ _ _ _ _)
         (hash-ref locked? (hash-ref unlock->user p fail) #f)]
        ; Must not use resource unless locked
        [(evt:call 'use p _ _ _ _ _)
         (hash-ref locked? (hash-ref use->user p fail) #f)]
        ; Otherwise, okay
        [_
         #t])
       ; Must not use anything after return
       (match evt
        [(evt:call 'lock p _ _ _ _ _)
         (not (hash-ref returned? (hash-ref lock->user p fail) #f))]
        [(evt:call 'unlock p _ _ _ _ _)
         (not (hash-ref returned? (hash-ref unlock->user p fail) #f))]
        [(evt:call 'use p _ _ _ _ _)
         (not (hash-ref returned? (hash-ref use->user p fail) #f))]
        ; Otherwise, okay
        [_
         #t]))))
  
  (provide/contract
   [use-resource
    (->t monitor 'server
         (->t monitor 'user
              (->t monitor 'lock void)
              (->t monitor 'use void)
              (->t monitor 'unlock void)
              any/c)
         any/c)]))

(module tester racket
  (require tests/eli-tester
           'lock)
  (test
   (use-resource
    (λ (lock use unlock)
      (lock) (use) (unlock)
      (lock) (use) (use) (unlock)))
   =>
   (void)
   
   (use-resource
    (λ (lock use unlock)
      (lock) (use) (unlock)
      (use-resource
       (λ (lock1 use1 unlock1)
         (lock1) (lock)
         (use) (use1)
         (unlock1) (unlock)))
      (lock) (use) (use) (unlock)))
   =>
   (void)
   
   (use-resource
    (λ (lock use unlock)
      (use)))
   =error>
   "disallowed"
   
   (use-resource
    (λ (lock use unlock)
      (lock) (use) (unlock) (unlock)))
   =error>
   "disallowed"
   
   (use-resource
    (λ (lock use unlock)
      (lock) (lock)))
   =error>
   "disallowed"
   
   (use-resource
    (λ (lock use unlock)
      (lock) (unlock) (use)))
   =error>
   "disallowed"
   
   ((use-resource (λ (lock use unlock) lock)))
   =error>
   "disallowed"
   
   ((use-resource (λ (lock use unlock) use)))
   =error>
   "disallowed"
   
   ((use-resource (λ (lock use unlock) unlock)))
   =error>
   "disallowed"
   ))

(require 'tester)
