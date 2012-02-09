#lang racket
(require rackunit)

;; Sort by an partial order that is incompletely specified.

(define (implies p q)
  (or (not p) q))

(define (partial-order-violations universe <=)
  (for/fold
   ([errors empty])
   ([a (in-list universe)])
   (append
    (if (<= a a)
        empty
        (list `(reflexivity ,a)))
    (for/fold
     ([errors empty])
     ([b (in-list universe)])
     (append
      (if (implies (and (<= a b) (<= b a))
                   (equal? a b))
          empty
          (list `(anti-symmetry ,a ,b)))
      (for/fold
       ([errors empty])
       ([c (in-list universe)])
       (append
        (if (implies (and (<= a b) (<= b c))
                     (<= a c))
            empty
            (list `(transitivity ,a ,b c)))
        errors))
      errors))
    errors)))

(check-pred empty? (partial-order-violations '(1 2 3 4 5) <=))
(check-equal? (partial-order-violations '(a)
                                        (λ (x y) #f))
              '((reflexivity a)))
(check-equal? (partial-order-violations '(a b)
                                        (match-lambda*
                                         ['(a a) #t]
                                         ['(b b) #t]
                                         ['(a b) #t]
                                         ['(b a) #t]))
              '((anti-symmetry b a)
                (anti-symmetry a b)))
(check-equal? (partial-order-violations '(a b c)
                                        (match-lambda*
                                         ['(a a) #t]
                                         ['(b b) #t]
                                         ['(c c) #t]
                                         ['(a b) #t]
                                         ['(b c) #t]
                                         ['(c a) #t]
                                         [_      #f]))
              '((transitivity c a c)
                (transitivity b c c)
                (transitivity a b c)))

;; (A A -> Bool u 'Unknown) -> (A A -> Bool)
(define (partial-fun->partial-order f)
  (define x-is-less-than-these (make-hasheq))
  (define (new-f x y)
    (define final-answer
      (match
       (f x y)
       [(? boolean? x) x]
       ['unknown
        (cond
         [(equal? x y)
          #t]
         ;; Look for anti-symmetry
         [(boolean? (f y x))
          (not (f y x))]
         [else
          ;; Look for transitivity
          (define trans-ans
            (for/fold ([ans 'unknown])
                      ([z (in-list (hash-ref x-is-less-than-these x empty))])
                      (cond
                       [(and (boolean? ans) ans)
                        ans]
                       [else
                        (define inner (f z y))
                        (if (equal? inner 'unknown)
                            ans
                            inner)])))
          (if (eq? trans-ans 'unknown)
              #f
              trans-ans)])]))
    (if final-answer
        (hash-update! x-is-less-than-these x (curry cons y) empty)
        (hash-update! x-is-less-than-these y (curry cons x) empty))
    final-answer)
  new-f)

(define (check-partial-fun->partial-order l f)
  (check-pred empty?
              (partial-order-violations l
                                        (partial-fun->partial-order f))))

(check-partial-fun->partial-order
 '(a)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('b 'c) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x y) (match* (x y)
                  [('b 'd) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x y) (match* (x y)
                  [('a 'c) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x y) (match* (x y)
                  [('a 'c) #t]
                  [('c 'b) #t]
                  [(_ _) 'unknown])))

(check-partial-fun->partial-order
 '(a c b)
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('b 'c) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a c b d)
 (λ (x y)
    (printf "~a ~a\n" x y)
    (match* (x y)
            [('a 'b) #t]
            [('b 'c) #t]
            [('c 'd) #t]
            [(_ _) 'unknown])))


