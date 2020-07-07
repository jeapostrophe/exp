#lang racket/base
(require pict)

(define (add-edge all from label to)
  (pin-arrow-line
   10 all
   from rc-find
   to lc-find
   #:line-width 3
   #:label (inset (text label) 5)))

(define (state ls)
  (frame (inset (apply vc-append (map text ls)) 5)))

(define p
  (let* ([initial (blank)]
         [local-private (state '("local" "private"))]
         [local-public (state '("local" "public"))]
         [consensus (state '("consensus"))]
         [p (hc-append 75
                       initial local-private
                       local-public consensus)]
         [p (add-edge p initial "" local-private)]
         [p (add-edge p local-private "declassify" local-public)]
         [p (add-edge p local-public "publish" consensus)]
         [p (inset p 25)])
    p))

(module+ main
  (require racket/gui/base)
  (show-pict (frame p)))
