#lang racket/base
(require racket/gui/base
         racket/class
         racket/snip)

(define reactive-snip%
  (class* snip% ()
    (init-field some-snip)
    
    (define-syntax-rule (delegate id)
      (define/override (id . a)
        (send/apply some-snip id a)))
    
    (delegate get-extent)
    (delegate draw)
    (delegate get-text)
    (define/override (copy)
      this)
    
    (inherit/super get-admin)
    (define/public (update! s)
      (set! some-snip s)
      (queue-callback
       (λ ()
         (send (get-admin) needs-update this 0 0 2000 2000))))
    
    (super-new)))

(provide reactive-snip%)