#lang racket

(define rubies 472302)

(define iron 0)
(define glass 0)

(define scope-cost 3000)
(define iron-cost 200)
(define glass-cost 150)

(define scope-sale 4100)

(for/or ([how-many-scopes-to-buy
          (in-range (floor (/ rubies scope-cost)) 0 -1)])
  (define how-many-iron-to-buy
    (max 0 (- how-many-scopes-to-buy iron)))
  (define how-many-glass-to-buy
    (max 0 (- how-many-scopes-to-buy glass)))
  (define post-rubies
    (- rubies
       (+ (* scope-cost how-many-scopes-to-buy)
          (* iron-cost how-many-iron-to-buy)
          (* glass-cost how-many-glass-to-buy))))
  (and (positive? post-rubies)
       (list 'scopes how-many-scopes-to-buy 
             'iron how-many-iron-to-buy
             'glass how-many-glass-to-buy)))