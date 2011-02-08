#lang racket
(require racket/require
         (path-up "temp-c/dsl.rkt")
         tests/eli-tester)


(define (test-spec spec)
  (define (f g) (g))
  (define f/c (contract spec f 'pos 'neg))
  
  (define x #f)
  (define s1 (make-semaphore))
  (define s2 (make-semaphore))
  (define t1
    (thread
     (λ ()
       (with-handlers ([exn? (λ (e) (set! x e))])
         (f/c
          (λ ()
            (semaphore-post s1)
            (semaphore-wait s2)))
         (semaphore-post s1)))))
  (define t2
    (thread
     (λ ()
       (with-handlers ([exn? (λ (e) (set! x e))])
         (semaphore-wait s1)
         (f/c
          (λ ()
            (semaphore-post s2)
            (semaphore-wait s1)))))))
  
  (thread-wait t1)
  (thread-wait t2)
  (when x
    (raise x)))

(define Race
  (with-monitor
      (label 'f ((label 'g (-> void?)) . -> . void?))
    (complement
     (seq _ (call 'f _)
          _ (call 'g)
          (call 'f _)
          _ (call 'g)
          (ret 'g _)
          (ret 'f _)
          (ret 'g _)
          (ret 'f _)))))
(define Concurrent
  (with-monitor
      (label 'f ((label 'g (-> void?)) . -> . void?))
    #:concurrent
    (complement
     (seq _ (call 'f _)
          _ (call 'g)
          (call 'f _)
          _ (call 'g)
          (ret 'g _)
          (ret 'f _)
          (ret 'g _)
          (ret 'f _)))))

(test
 (test-spec Race) => (void)
 (test-spec Concurrent) =error> "disallowed")