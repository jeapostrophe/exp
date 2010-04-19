#lang scheme

(define dice<%>
  (interface () roll max crit))

(define dice/c
  (object-contract
   [roll (-> exact-nonnegative-integer?)]
   [max (-> exact-nonnegative-integer?)]
   [crit (-> exact-nonnegative-integer?)]))

(provide/contract
 [dice<%> interface?]
 [dice/c contract?])

(define (make-n-dice% n)
  (class* object% (dice<%>)
    (define/public (roll)
      (add1 (random n)))
    (define/public (max)
      n)
    (define/public (crit) (max))
    (super-new)))

(define d4 (new (make-n-dice% 4)))
(define d6 (new (make-n-dice% 6)))
(define d8 (new (make-n-dice% 8)))
(define d10 (new (make-n-dice% 10)))
(define d12 (new (make-n-dice% 12)))
(define d20 (new (make-n-dice% 20)))

(provide/contract
 [d4 dice/c]
 [d6 dice/c]
 [d8 dice/c]
 [d10 dice/c]
 [d12 dice/c]
 [d20 dice/c])

(define (make-ndm-dice n dm)
  (new 
   (class* object% (dice<%>)
     (define/public (roll)
       (for/fold ([sum 0])
         ([_ (in-range 0 n)])
         (+ sum (send dm roll))))
     (define/public (max)
       (* n (send dm max)))
     (define/public (crit) (max))
     (super-new))))

(define d3*6 (make-ndm-dice 3 d6))

(provide/contract
 [make-ndm-dice (exact-nonnegative-integer? dice/c . -> . dice/c)])

(define (make-die+bonus d bonus)
  (new
   (class* object% (dice<%>)
     (define/public (roll)
       (+ (send d roll) bonus))
     (define/public (max)
       (+ (send d max) bonus))
     (define/public (crit) (max))
     (super-new))))

(provide/contract
 [make-die+bonus (dice/c exact-integer? . -> . dice/c)])

(define (make-die+crit-bonus d cd)
  (new
   (class* object% (dice<%>)
     (define/public (roll)
       (send d roll))
     (define/public (max)
       (send d max))
     (define/public (crit)
       (+ (send d crit)
          (send cd roll)))
     (super-new))))

(provide/contract
 [make-die+crit-bonus (dice/c dice/c . -> . dice/c)])

(define zero-die
  (new
   (class* object% (dice<%>)
         (define/public (roll) 0)
         (define/public (max) 0)
         (define/public (crit) 0)
         (super-new))))

(define (make-die-sum2 d1 d2)
  (new 
   (class* object% (dice<%>)
         (define/public (roll)
           (+ (send d1 roll)
              (send d2 roll)))
         (define/public (max)
           (+ (send d1 max)
              (send d2 max)))
         (define/public (crit)
           (+ (send d1 crit)
              (send d2 crit)))
         (super-new))))
(define (make-die-sum . ds)
  (foldl make-die-sum2
         zero-die ds))

(provide/contract
 [make-die-sum (() () #:rest (listof dice/c) . ->* . dice/c)])
