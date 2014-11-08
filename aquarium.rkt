#lang racket/base
(require racket/match)

(define (make-world w h f)
  (build-vector w (λ (x) (build-vector h (λ (y) (f x y))))))

(define (world-ref w h world x y)
  (if (and (<= 0 x (sub1 w))
           (<= 0 y (sub1 h)))
      (vector-ref (vector-ref world x) y)
      #f))

(define (world-set! world x y v)
  (vector-set! (vector-ref world x) y v))

(define (random-list-ref l)
  (list-ref l (random (length l))))

(define (random-color)
  (random-list-ref '("red" "orange" "yellow" "green" "blue" "indigo" "violet")))

(define FRAMES 3)

(define (random-fish)
  (cons (random-color) (random FRAMES)))

(define (tick w h world)
  (define new-world (make-world w h (λ (x y) #f)))
  (for* ([x (in-range w)]
         [y (in-range h)])
    (define live? (world-ref w h world x y))
    (define neighbor-count
      (for*/sum ([dx (in-range -1 2)]
                 [dy (in-range -1 2)]
                 #:unless (= dx dy 0))
        (if (world-ref w h world (+ x dx) (+ y dy))
            1
            0)))
    (world-set!
     new-world x y
     (cond
      [(and live? (< neighbor-count 2))
       #f]
      [(and live? (<= 2 neighbor-count 3))
       (match-define (cons col fr) live?)
       (cons col (modulo (+ 1 fr) FRAMES))]
      [(and live? (< 3 neighbor-count))
       #f]
      [(and (not live?) (= 3 neighbor-count))
       (random-fish)]
      [else
       #f])))
  new-world)

(require pict)
(define (show w h cw ch world)
  (for/fold ([img (blank)])
            ([x (in-range w)])
    (vc-append
     img
     (for/fold ([img (blank)])
               ([y (in-range h)])
       (define live? (world-ref w h world x y))
       (hc-append img
                  (frame
                   (if live?
                       (standard-fish cw ch
                                      #:color (car live?)
                                      #:open-mouth (/ (cdr live?) FRAMES))
                       (blank cw ch))))))))

(module+ main
  (require 2htdp/universe)
  (define cw 800)
  (define ch 600)
  (define w 16)
  (define h 16)
  (define (random-aquarium)
    (make-world w h
                (λ (x y) (and (zero? (random 2))
                              (cons (random-color)
                                    (random FRAMES))))))
  (void
   (big-bang
    (random-aquarium)
    (on-key
     (λ (last ke)
       (random-aquarium)))
    (on-tick
     (λ (last) (tick w h last)))
    (on-draw
     (λ (last) (pict->bitmap (scale-to-fit (show w h cw ch last) cw ch)))))))
