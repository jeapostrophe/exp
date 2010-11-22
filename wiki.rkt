#lang racket
(require racket/runtime-path
         web-server/dispatchers/dispatch
         web-server/servlet
         web-server/servlet-env)

; Library
(define (thread-wait* . ts)
  (for-each thread-wait ts))

(define (printing-output* thunk)
  (make-response/incremental
   200 #"OK" (current-seconds)
   #"text/html"
   empty
   (λ (output-bytes)
     (define-values (out in) (make-pipe))
     (thread-wait*
      (thread 
       (λ ()
         (parameterize ([current-output-port in])
           (thunk))
         (close-output-port in)))
      (thread 
       (λ ()
         (let loop ()
           (define bs (read-bytes-line out))
           (unless (eof-object? bs)
             (output-bytes bs)
             (loop)))))))))
(define-syntax-rule (printing-output e ...)
  (printing-output* (λ () e ...)))

; Put your verbs
(define (create req path)
  (printing-output
   (printf "~s\n" path)))

; Bounce to file dispatcher
(define (static req url-path)
  ; XXX Check for going outside static-root with .., etc
  (define real-path (apply build-path static-root url-path))
  (if (file-exists? real-path)
      (next-dispatcher)
      (redirect-to (top-url create url-path))))

(define-values (top-dispatch top-url)
  (dispatch-rules
   ; Put more verbs here
   [("wiki" "create" (string-arg) ...) create]
   [((string-arg) ...) static]))

; Set to the appropriate place
(define-runtime-path static-root ".")
(serve/servlet top-dispatch
               ; Comment-in to not launch
               ;#:command-line? #t
               #:port 8080
               #:extra-files-paths (list static-root)
               #:servlet-path "/Main"
               #:servlet-regexp #rx"")