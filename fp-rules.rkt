#lang racket

;; fp rules
(define fprops (make-weak-hash))
(define (fprop-set stx k v)
  (printf "~v: ~v = ~v!\n" stx k v)
  (hash-update! fprops stx
                (λ (ht) (hash-set ht k v))
                (λ () (hasheq)))
  stx)
(define (fprop-get stx k)
  (define ans
    (hash-ref (hash-ref fprops stx (λ () (hasheq)))
            k
            #f))
  (printf "~v: ~v = ~v\n" stx k ans)
  ans)

(define (safe+ x y)
  (and x y (+ x y)))
(define (safe-zero? x)
  (and (number? x) (zero? x)))

(define (fexpand stx)
  (define my-+
    (match-lambda
     [`(+ ,lhs ,rhs)
      (cond
       [(safe-zero? (fprop-get lhs 'num))
        rhs]
       [(safe-zero? (fprop-get rhs 'num))
        lhs]
       [else
        (define ans (safe+ (fprop-get lhs 'num)
                           (fprop-get rhs 'num)))
        (fprop-set stx 'num ans)
        (if ans
            ans
            `(real+ ,lhs ,rhs))])]))
  (define my-datum
    (match-lambda
     [(? number? n)
      (fprop-set n
                 'num
                 n)]))

  (define changed? #f)
  (define fix (make-hash))
  (define (consult-fix stx)
    (cond
     [(hash-has-key? fix stx)
      (hash-ref fix stx)]
     [(list? stx)
      (map consult-fix stx)]
     [else
      stx]))
  (define (fexpand/inner stx)
    (printf "~v\n" `(fexpand/inner ,stx))
    (match stx
           [(list-rest '+ inner)
            (my-+ stx #;(cons '+ (consult-fix inner)))]
           [(? number?)
            (my-datum stx #;(consult-fix stx))]
           [(? symbol?)
            stx]
           [(list-rest 'real+ es)
            (cons 'real+ (map fexpand/outer es))]))
  (define (fexpand/outer stx)
    (printf "~v\n" `(fexpand/outer ,stx))
    (define last (hash-ref fix stx #f))
    (define after (fexpand/inner stx))
    (printf "~v ==> ~v [~v]\n" stx after last)
    (unless (equal? last after)
            (hash-set! fix stx after)
            (set! changed? #t))
    (if (equal? stx after)
        after
        (fexpand/outer after)))
  (define (fexpand/fix stx)
    (printf "~v\n" `(fexpand/fix ,stx))
    (set! changed? #f)
    (define after (fexpand/outer stx))
    (if changed?
        (fexpand/fix stx)
        after))
  (fexpand/fix stx))

;; tests
(require tests/eli-tester)

(test
 (fexpand `(+ 0 1)) => `1
 (fexpand `(+ 1 0)) => `1
 (fexpand `(+ x 0)) => `x
 (fexpand `(+ 0 x)) => `x
 (fexpand `(+ 1 3)) => `4
 (fexpand `(+ -1 1)) => `0
 (fexpand `(+ 1 x)) => `(real+ 1 x)
 (printf "\n\nBing\n\n")
 (fexpand `(+ 3 (+ -1 1))) => `3
 )
