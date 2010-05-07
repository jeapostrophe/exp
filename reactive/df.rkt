#lang racket
(require (for-syntax racket/function)
         racket/stxparam)

; general
(define-syntax-rule (while cond e ...)
  (let loop () (when cond (let () e ... (loop)))))

(define (vector-ormap f v)
  (for/or ([e (in-vector v)]) (f e)))

; tee-channels

(struct a-tee-channel (manager-t put-ch service-ch))
(struct tee:listen (reply-ch))
(struct tee:disconnect (listener-ch))

(define (tee-channel)
  (define put-ch (make-channel))
  (define service-ch (make-channel))
  (define (manage listeners)
    (sync
     (handle-evt put-ch
                 (λ (new-v)
                   ; XXX thread resume?
                   (for-each (λ (ch) (channel-put ch new-v)) listeners)
                   (manage listeners)))
     (handle-evt service-ch
                 (match-lambda
                   [(tee:listen reply-ch)
                    ; XXX could reuse reply-ch
                    (define new-l (make-channel))
                    (channel-put reply-ch new-l)
                    (manage (list* new-l listeners))]
                   [(tee:disconnect l)
                    (manage (remq l listeners))]))))
  (define manager-t (thread (λ () (manage empty))))
  (a-tee-channel manager-t put-ch service-ch))

(define (tee-channel-put tc v)
  (match-define (a-tee-channel manager-t put-ch service-ch) tc)
  (thread-resume manager-t)
  (channel-put put-ch v))

(define (tee-channel-listen tc)
  (match-define (a-tee-channel manager-t put-ch service-ch) tc)
  (define reply-ch (make-channel))
  (thread-resume manager-t)
  (channel-put service-ch (tee:listen reply-ch))
  (channel-get reply-ch))

(define (tee-channel-disconnect tc l)
  (match-define (a-tee-channel manager-t put-ch service-ch) tc)
  (thread-resume manager-t)
  (channel-put service-ch (tee:disconnect l)))

; n channel get

(define (channels-get . chs)
  (apply values (map channel-get chs)))

; Reactors

(define-syntax-parameter emit
  (curry raise-syntax-error 'emit "Only allowed inside reactor"))

(define-syntax-rule (reactor e ...)
  (reactor* (λ (to-emit) 
              (syntax-parameterize ([emit (make-rename-transformer #'to-emit)])
                                   e ...))))

(struct a-reactor (thread tee-channel))

(require racket/gui)
(define (reactor* emitter)
  (define ch (tee-channel))
  
  ; XXX
  (define f (new frame% [label "Reactor"]))
  (define m (new message% [parent f] [label "undefined"] [auto-resize #t]))
  
  (define (to-emit v)
    ; XXX
    (send m set-label (format "~S" v))
    
    (tee-channel-put ch v))
  
  ; XXX
  (send f show #t)
  
  (a-reactor
   (thread (λ () (emitter to-emit)))
   ch))

(define (emit->idempotent-emit emit)
  (define last (gensym 'uniq))
  (λ (new)
    (unless (equal? last new)
      (set! last new)
      (emit new))))

(define 
  (make-clock time-now)
  (reactor
   (define real-emit (emit->idempotent-emit emit))
   (while #t
          (real-emit (time-now)))))

(define clock (make-clock current-inexact-milliseconds))

; Lifting
(define (always-channel v)
  (define ch (make-channel))
  (thread (λ () (while #t (channel-put ch v))))
  ch)

(define ->channel
  (match-lambda
    [(a-reactor t tc)
     (thread-resume t)
     (tee-channel-listen tc)]
    [v
     (always-channel v)]))

(define (lift f . args)
  (reactor
   (define chs (map ->channel (list* f args)))
   (while #t
          (call-with-values (λ () (apply channels-get chs))
                            (λ (fv . argsv)
                              (emit (apply fv argsv)))))))

; Events
(struct an-event (reactor q))

(define (event)
  (define q (make-channel))
  (an-event (reactor 
             (define clock-ch (->channel clock))
             (while #t 
                    ; Synchronize with the clock
                    (channel-get clock-ch)
                    (emit (channel-get q))))
            q))
(define event-send! 
  (match-lambda*
    [(list (an-event _ q) v) (channel-put q v)]))

; Examples
(define inexact-milliseconds clock)

(define 
  seconds
  (reactor
   (define ms-ch (->channel inexact-milliseconds))
   (while #t
          (define ms (channel-get ms-ch))
          (emit (inexact->exact (floor (/ ms 1000)))))))
(define add1-seconds
  (lift add1 seconds))
(define <secs
  (lift < seconds add1-seconds))
