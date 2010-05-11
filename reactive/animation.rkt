#lang racket/gui
(require 2htdp/image
         "df.rkt"
         (only-in mrlib/image-core
                  render-image))

(define MIN-WIDTH 640)
(define MIN-HEIGHT 480)

(define the-animation-graphic
  (cell (empty-scene MIN-WIDTH MIN-HEIGHT))) 

(define the-animation-graphic-behavior
  (cell-behavior the-animation-graphic))

(define the-animation-frame
  (local
    [(define f 
       (new frame% [label "Reactive Racket Animation"]))
     (define c
       (new canvas% 
            [parent f]
            [min-width MIN-WIDTH]
            [min-height MIN-HEIGHT]
            [paint-callback
             (λ (c dc)
               (send dc set-smoothing 'aligned)
               (render-image (value-now the-animation-graphic-behavior) dc 0 0))]))]
    (send f show #t)
    
    (reactor
     (define ch (->channel the-animation-graphic-behavior))
     (while #t
            (channel-get ch)
            (send c refresh)))
    
    f))

(set-cell! the-animation-graphic
           (lift place-image (lift triangle (lift + 32 (lift * 5 (lift modulo seconds 100))) "solid" "red")
                 (/ MIN-WIDTH 2) (/ MIN-HEIGHT 2)
                 (empty-scene MIN-WIDTH MIN-HEIGHT)))