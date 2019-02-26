#lang racket/base
(require pict
         racket/math
         racket/match)

(define (xout p)
  (pin-line (pin-line p
                      p rt-find p lb-find)
            p lt-find p rb-find))

(define (combine base ps)
  (for/fold ([b base]) ([xyp (in-list ps)])
    (match-define (vector dx dy p) xyp)
    (pin-over b dx dy p)))

(define whole-area (rectangle 156 118))

(define stall-mat
  (filled-rectangle 48 72
                    #:border-color "black"
                    #:color "brown"))
(define h-mat (rotate stall-mat (* pi 1/2)))

(define plywood
  (filled-rectangle 48 96
                    #:border-color "black"
                    #:color "tan"))
(define h-ply
  (filled-rectangle 72 48
                    #:border-color "black"
                    #:color "tan"))

(define r-3bt-power-rack (filled-rectangle 40 53 #:color "red"))

(define spotter-arms1 (filled-rectangle 24 3 #:color "yellow"))
(define spotter-arms (vl-append spotter-arms1
                                (blank 1 (+ 53 -3 -3))
                                spotter-arms1))

(define plate-storage1 (filled-rectangle 17.5 13 #:color "yellow"))
(define plate-storage-one
  (hc-append plate-storage1 (blank (+ 1.5 30 1.5) 1)))
(define plate-storage-two
  (hc-append plate-storage1
             (blank (+ 1.5 30 1.5 (* -1/2 17.5) (* -1/2 17.5))
                    1)
             plate-storage1))

(define shrimp-trawler (filled-rectangle 3 43 #:color "yellow"))
(define utility-bench (filled-rectangle 14 48 #:color "green"))
(define ring (filled-ellipse 4.75 4.75 #:color "orange"))

(define rack-setup
  (combine (vc-append plate-storage-two
                      (cc-superimpose r-3bt-power-rack (arrow 15 0))
                      plate-storage-two)
           (list (vector r-3bt-power-rack rt-find spotter-arms)
                 #;(vector 42.5 -30 shrimp-trawler))))

(define vert-option
  (combine whole-area
           (list (vector 0 0 (vc-append (ht-append h-mat h-mat)
                                        (ht-append h-mat h-mat)))
                 (vector 12 12 (rotate rack-setup (/ pi -2)))
                 (vector (* 10.5 12) 24 utility-bench)
                 (vector 100 (+ 42 (/ 4.75 2)) ring)
                 (vector 100 (+ 42 4.75 12.5 (/ 4.75 2)) ring))))

(define horiz-option
  (combine whole-area
           (list (vector 0 0 (vc-append (ht-append h-ply h-ply)
                                        (ht-append h-ply h-ply)))
                 (vector 0 0 (ht-append plywood plywood plywood))
                 (vector 0 0 (vc-append (ht-append h-mat h-mat)
                                        (ht-append h-mat h-mat)))                 
                 (vector 12 12 rack-setup)
                 (vector (* 7 12) (* 6.5 12) (rotate utility-bench (/ pi 2)))
                 (vector 100 (+ 42 (/ 4.75 2)) ring)
                 (vector 100 (+ 42 4.75 12.5 (/ 4.75 2)) ring))))

(define the-basement
  horiz-option)

(module+ main
  (require racket/gui/base)
  (show-pict (scale (inset the-basement 12) 4)))
