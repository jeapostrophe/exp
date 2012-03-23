#lang racket/base
(require web-server/configuration/namespace
         web-server/servlet-env)

(define (dynamic-require/no-attach modpath sym)
  (parameterize ([current-namespace ((make-make-servlet-namespace) #:additional-specs '(web-server/http))])
    (dynamic-require modpath sym)))

(define (dev-mode path start->server)
  (define (get)
    (file-or-directory-modify-seconds path))
  (let loop ()
    (define init-time
      (get))
    (define server-cust
      (let ([c (make-custodian)])
        (parameterize ([current-custodian c])
          (thread (lambda () (start->server (dynamic-require/no-attach `(file ,path) 'start)))))
        c))
    (let wait ()
      (define now (get))
      (if (now . > . init-time)
        (begin (custodian-shutdown-all server-cust)
               (loop))
        (begin (sleep 1)
               (wait))))))

(dev-mode "a.rkt"
          (λ (start)
            (serve/servlet start
                           #:port 0)))

