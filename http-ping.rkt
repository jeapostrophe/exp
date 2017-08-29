#lang racket/base
(require net/http-client
         racket/list
         math/base
         racket/format
         racket/port)

(define (fmt-time ms)
  (~a (~r ms #:precision '(= 2) #:min-width 10) "ms"))

(define (http-ping host)
  (define start (current-inexact-milliseconds))
  (with-handlers ([exn:fail? (λ (x) #f)])
    (eprintf "> ~a\n" host)
    (define-values (st hd body-p) (http-sendrecv host "/"))
    (copy-port body-p (open-output-nowhere))
    (define end (current-inexact-milliseconds))
    (define v (- end start))
    (eprintf "< ~a = ~a\n" (~a #:min-width 14 host) (fmt-time v))
    v))

(define (http-pings H)
  (define T
    (for/list ([h (in-list H)])
      (define v (box #f))
      (define t (thread (λ () (set-box! v (http-ping h)))))
      (λ ()
        (thread-wait t)
        (unbox v))))
  (map (λ (x) (x)) T))

(define (display-stats aV)
  (define-values (nV V) (partition not aV))
  (printf "\n")
  (printf "Fails: ~a\n" (length nV))
  (printf "  Min: ~a\n" (fmt-time (apply min V)))
  (printf "  Max: ~a\n" (fmt-time (apply max V)))
  (printf "  Avg: ~a\n" (fmt-time (/ (sum V) (length V)))))

(module+ main
  (define N 20)
  (define H '("google.com" "fitbit.com" "yahoo.com" "amazon.com" "ebay.com" "facebook.com" "airbnb.com" "uber.com" "lds.org" "twitter.com" "instagram.com" "microsoft.com"))
  (define H*N
    (append* (make-list N H)))
  (display-stats (http-pings (shuffle H*N))))
