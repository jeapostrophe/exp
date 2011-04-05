#lang scheme
(require scheme/gui)

(define reactive-prompt (make-continuation-prompt-tag 'reactive))
(define command-prompt (make-continuation-prompt-tag 'command))

(define-struct cell ([now #:mutable]))
(define-struct demand (k))

(define (commands command-f)
  (when (continuation-prompt-available? command-prompt)
    (call-with-current-continuation
     (lambda (reactive-k)
       ; reactive-k accepts time-varying values
       (reactive-k (command-f)))
     command-prompt)))

(define (command-prompt-handler)
  (printf "Aborted!~n"))

(define reactive-initialization (make-parameter #f))

; Two continuations matter during propagation. init-k identifies the node that received the new value.
; When control returns to init-k, the current continuation is up-to-date. Call return-k with the
; current continuation.
(define-struct reaction (return-k identity))

(define (current-reaction)
  (let ([marks (continuation-mark-set->list (current-continuation-marks) 'reaction)])
    (if (empty? marks)
        #f
        (first marks))))

(define (get-recompute-thunk k)
  (let ([marks (continuation-mark-set->list (continuation-marks k) 'recompute)])
    (if (empty? marks)
        #f
        (first marks))))

(define (make-timer interval callback)
  (new timer%
       [notify-callback callback]
       [interval (* interval 1000)]
       [just-once? #f]))

(define (timer v txt interval)
  (call-with-composable-continuation
   (lambda (k)
     (if (reactive-initialization)
         ;;;
         ;;; Intialization effects
         ;;;
         (begin
           (printf "Initializing timer ~a~n" txt)
           (set-cell-now! v (current-seconds))
           (make-timer
            interval
            (lambda ()
              (set-cell-now! v (current-seconds))
              (printf "Tick ~a at ~a~n" txt (cell-now v))
              ;;;
              ;;; Dataflow (part 1 of 2)
              ;;;
              (let ([updated-k
                     (call-with-current-continuation
                      (lambda (done-k)
                        (call-with-continuation-prompt
                         (lambda ()
                           (call-with-continuation-prompt
                            (lambda ()
                              (with-continuation-mark 'reaction (make-reaction done-k v)
                                (let ([recompute (get-recompute-thunk k)])
                               (if recompute
                                   recompute
                                   (k (cell-now v))))))
                            reactive-prompt))
                         command-prompt
                         command-prompt-handler)))])
                (when (continuation? updated-k)
                  (updated-k (cell-now v))))))
           ; Initial value of the behavior
           (printf "Returning initial value for ~a~n" txt)
           (with-continuation-mark 'recompute (lambda () (k (cell-now v)))
             (k (cell-now v)))
           (abort-current-continuation command-prompt))
         ;;;
         ;;; Dataflow (part 2 of 2)
         ;;;
         (let ([reaction (current-reaction)])
           (if (eq? v (reaction-identity reaction))
               ((reaction-return-k reaction) k)
               (k (cell-now v)))
           (abort-current-continuation command-prompt))))
   reactive-prompt))


(define frame (new frame% [label "Current Value"] [height 80] [width 300]))
(define msg (new message% [parent frame] [label ""] [min-width 300]))
(send frame show #t)


(let ([v1 (make-cell #f)]
      [v2 (make-cell #f)])
  (parameterize
      ([reactive-initialization #t])
    (call-with-continuation-prompt
     (lambda ()
       (with-continuation-mark
           'reaction (make-reaction (lambda () (error "whoa")) #f)
         (with-continuation-mark
             'recompute (lambda () (error "omg"))
           (call-with-continuation-prompt
            (lambda ()
              (let ([t1 (timer v1 "first" 1)]
                    [t2 (timer v2 "second" 1)])
                
                (send msg set-label (format "~a *** ~a *** ~a" 
                                            (build-list (modulo t1 10) (λ (n) n))
                                            (- t1 t2)
                                            (if (zero? (modulo t2 2))
                                                "NO ERRORS"
                                                (/ 1 (modulo t2 2)))
                                            ))))
            reactive-prompt))))
     command-prompt
     command-prompt-handler)))