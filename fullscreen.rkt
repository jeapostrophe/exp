#lang racket/gui

(define-values (w h) (get-display-size #t))
(define-values (w^ h^) (get-display-size #f))

; Make a frame by instantiating the frame% class
(define frame 
  (new frame% 
       [label "Example"]
       [x 0]
       [y (- h^ h -4)]
       [width w]
       [height h]
       [style '(hide-menu-bar no-resize-border no-caption no-system-menu)]))

(define canvas
  (new canvas%
       [parent frame]
       [min-width w]
       [min-height h]
       [paint-callback
        (λ (c dc)
          (send dc set-background "black")
          
          (send dc clear)
          
          (send dc set-pen "white" 10 'solid)
          (send dc draw-point 0 0)
          (send dc draw-point w h)
          
          (send dc set-pen "red" 10 'solid)
          (send dc draw-point w^ h^))]))

; Show the frame by calling its show method
(send frame show #t)