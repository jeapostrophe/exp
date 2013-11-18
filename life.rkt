#lang racket/base
(require data/gvector
         racket/string)

(define (bitwise-bit-set n m)
  (bitwise-ior n (arithmetic-shift 1 m)))

(struct dish (rows cols gv) #:prefab)

(define (string->dish s)
  (define rows (string-split s))
  (define how-many-rows (length rows))
  (define the-gv (make-gvector))
  (define how-many-cols
    (for/fold ([hmc 0])
     ([i (in-naturals)]
      [r (in-list rows)])
     (define rn (gvector-ref the-gv i 0))
     (define new-rn
       (for/fold ([new-rn rn])
           ([j (in-naturals)]
            [c (in-string r)])
         (if (char=? #\O c)
           (bitwise-bit-set new-rn j)
           new-rn)))
     (gvector-set! the-gv i new-rn)
     (max hmc (string-length r))))
  (dish how-many-rows how-many-cols the-gv))

(define (let-there-be-life s)
  (define d (string->dish s))
  d)

(module+ test
  (let-there-be-life
   "........................O...........
    ......................O.O...........
    ............OO......OO............OO
    ...........O...O....OO............OO
    OO........O.....O...OO..............
    OO........O...O.OO....O.O...........
    ..........O.....O.......O...........
    ...........O...O....................
    ............OO......................"))
