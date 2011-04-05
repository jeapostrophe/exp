#lang racket
(require (for-syntax racket/function)
         racket/async-channel
         racket/stxparam)

(provide (all-defined-out))

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

(define (tee-channel-disconnect! tc l)
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
  (reactor/init undefined-const e ...))

(define-syntax-rule (reactor/init init e ...)
  (reactor* init
            (λ (to-emit) 
              (syntax-parameterize ([emit (make-rename-transformer #'to-emit)])
                                   e ...))))

(struct a-reactor ([last-value #:mutable] thread tee-channel))

(define undefined-const
  (local [(define x x)] x))

(define (reactor* init emitter)
  (define ch (tee-channel))
  (define r
    (a-reactor
     init
     (thread (λ () (emitter to-emit)))
     ch))
  
  (define (to-emit v)
    (set-a-reactor-last-value! r v)
    (tee-channel-put ch v))
  
  r)

(define value-now
  (match-lambda
    [(? a-reactor? r)
     (a-reactor-last-value r)]
    [v v]))

(define (emit->idempotent-emit emit)
  (define last (gensym 'uniq))
  (λ (new)
    (unless (equal? last new)
      (set! last new)
      (emit new))))

(define clock-res current-inexact-milliseconds)

(define clock
  (reactor
   (define real-emit (emit->idempotent-emit emit))
   (while #t
          (real-emit (clock-res)))))

; Lifting
(define (always-channel v)
  (define ch (make-channel))
  (thread (λ () (while #t (channel-put ch v))))
  ch)

(define ->channel
  (match-lambda
    [(a-reactor lv t tc)
     (thread-resume t)
     (tee-channel-listen tc)]
    [v
     (always-channel v)]))

(define *-disconnect!
  (match-lambda*
    [(list (a-reactor lv t tc) l)
     (thread-resume t)
     (tee-channel-disconnect! tc l)]
    [(list _ _)
     (void)]))

(define (lift f . args)
  (reactor
   ; XXX optimize constants
   (define chs (map ->channel (list* f args)))
   (while #t
          (call-with-values (λ () (apply channels-get chs))
                            (λ (fv . argsv)
                              (emit (apply fv argsv)))))))

; Events
(struct an-event (reactor q))

(define (event)
  (define q (make-async-channel))
  (an-event (reactor
             (define clock-ch (->channel clock))
             (while #t 
                    (match-define (cons v-time v) (async-channel-get q))
                    (let loop ()
                      (define n-time (channel-get clock-ch))
                      (if (v-time . <= . n-time)
                          (emit v)
                          (loop)))))
            q))
(define event-send! 
  (match-lambda*
    [(list (an-event _ q) v)
     (async-channel-put q (cons (clock-res) v))]))

; Cells
(struct a-cell ([src-sig #:mutable]
                [src-ch #:mutable]
                sig))
                
(define (cell init)
  (define ready? (make-semaphore))
  (define this
    (a-cell init (->channel init)
            (reactor/init
             (value-now init)
             (semaphore-wait ready?)
             (while #t
                    (emit (channel-get (a-cell-src-ch this)))))))
  (semaphore-post ready?)
  this)

(define cell-behavior a-cell-sig)

(define (set-cell! c v)
  (define v-ch (->channel v))
  (match-define (a-cell src-sig src-ch _) c)
  (*-disconnect! src-sig src-ch)
  ; XXX Race
  (set-a-cell-src-sig! c v)
  (set-a-cell-src-ch! c v-ch))

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
