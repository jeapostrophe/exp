#lang racket
(require racket/package
         rackunit)

;; Sort by an partial order that is incompletely specified.

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

;; (A -> (listof A) (A A -> Bool u 'Unknown) -> (A A -> Bool)
(define (partial-fun->partial-order x-is-less-than f)
  (define faked (make-hash))
  (define (fake-f x y)
    (if (hash-has-key? faked (cons x y))
        #t
        (f x y)))
  (define (new-f x y)
    (match
     (fake-f x y)
     [(? boolean? x) x]
     ['unknown
      (cond
       [(equal? x y)
        #t]
       ;; Look for anti-symmetry
       [(boolean? (fake-f y x))
        (not (fake-f y x))]
       [else
        ;; Look for transitivity
        (define trans-ans
          (for/fold ([ans 'unknown])
                    ([z (in-list (x-is-less-than x))])
                    (cond
                     [(and (boolean? ans) ans)
                      ans]
                     [else
                      (define inner (new-f z y))
                      (if (equal? inner 'unknown)
                          ans
                          inner)])))
        (if (eq? trans-ans 'unknown)
            (begin #;(printf "decided ~a <= ~a\n" y x)
              (hash-set! faked (cons y x) #t)
              #f)
            trans-ans)])]))
  new-f)

(define (check-partial-fun->partial-order l x-> f)
  (test-pred (format "~a ~a ~a" l x-> f)
             empty?
             (partial-order-violations l
                                       (partial-fun->partial-order x-> f))))

(check-partial-fun->partial-order
 '(a)
 (λ (x) empty)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b)
 (λ (x) empty)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x) empty)
 (λ (x y) 'unknown))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x) (match x
               ['a '(b)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('b 'c) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x) (match x
               ['a '(b)]
               ['c '(d)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x) (match x
               ['b '(d)]
               ['c '(d)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('b 'd) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x) (match x
               ['a '(c)]
               ['c '(d)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'c) #t]
                  [('c 'd) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a b c d)
 (λ (x) (match x
               ['a '(c)]
               ['c '(b)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'c) #t]
                  [('c 'b) #t]
                  [(_ _) 'unknown])))

(check-partial-fun->partial-order
 '(a c b)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               [_ empty]))
 (λ (x y) (match* (x y)
                  [('a 'b) #t]
                  [('b 'c) #t]
                  [(_ _) 'unknown])))
(check-partial-fun->partial-order
 '(a c b d)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               ['c '(d)]
               [_ empty]))
 (λ (x y)
    (match* (x y)
            [('a 'b) #t]
            [('b 'c) #t]
            [('c 'd) #t]
            [(_ _) 'unknown])))


(check-partial-fun->partial-order
 '(a d b c)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               ['c '(d)]
               [_ empty]))
 (λ (x y)
    (match* (x y)
            [('a 'b) #t]
            [('b 'c) #t]
            [('c 'd) #t]
            [(_ _) 'unknown])))

(check-partial-fun->partial-order
 '(a b d c)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               ['c '(d)]
               [_ empty]))
 (λ (x y)
    (match* (x y)
            [('a 'b) #t]
            [('b 'c) #t]
            [('c 'd) #t]
            [(_ _) 'unknown])))

(check-partial-fun->partial-order
 '(b d a c)
 (λ (x) (match x
               ['a '(b)]
               ['b '(c)]
               ['c '(d)]
               [_ empty]))
 (λ (x y)
    (match* (x y)
            [('a 'b) #t]
            [('b 'c) #t]
            [('c 'd) #t]
            [(_ _) 'unknown])))

;; (-> (listof (cons A A))) -> (A -> (listof A) x (A A -> Bool u 'Unknown)
(define (observations->partial-fun get-obvs)
  (define (x-is-less-than x)
    (filter-map (λ (a*b) (and (eq? (car a*b) x)
                              (cdr a*b)))
                (get-obvs)))
  (define (<= x y)
    (or (and (member (cons x y) (get-obvs)) #t)
        'unknown))
  (values x-is-less-than
          <=))

(package-begin
  (define-values (x-is-less-than <=) (observations->partial-fun (λ () '((a . b) (b . c) (c . d)))))
  (check-partial-fun->partial-order
   '(a b c d) x-is-less-than <=))

(provide (all-defined-out))
