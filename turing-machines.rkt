#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/match
         racket/list)

(struct *tm (initial blank final? delta))
(define-syntax (tm stx)
  (syntax-parse stx
    [(_ #:Q (state ...)
        #:G (sym ...)
        #:b blank
        #:S (input ...)
        #:q0 initial-state
        #:F (final-state ...)
        #:delta
        [(delta-state delta-symbol)
         (~literal ->)
         (next-state write-symbol head-movement)]
        ...)
     (syntax/loc stx
       (*tm 'initial-state
            'blank
            (λ (some-state)
              (or (eq? some-state 'final-state) ...))
            (λ (some-state some-symbol)
              (match* (some-state some-symbol)
                [('delta-state 'delta-symbol)
                 (values 'next-state 'write-symbol 'head-movement)]
                ...
                [(_ _)
                 (error 'tm-delta "Partial on ~v and ~v"
                        some-state some-symbol)]))))]))

(struct tape (before after))
(define empty-tape (tape empty empty))
(define (tape-read t b)
  (match-define (tape before after) t)
  (match after
    [(cons h _) h]
    [(list) b]))
(define (tape-move t b dir)
  (match-define (tape before after) t)
  (match dir
    ['L
     (match after
       [(cons a-hd a-tl)
        (tape (cons a-hd before) a-tl)]
       [(list)
        (tape (cons b before) empty)])]
    ['R
     (match before
       [(cons b-hd b-tl)
        (tape b-tl (cons b-hd after))]
       [(list)
        (tape empty (cons b after))])]
    [_
     (error 'tape-move "Given direction (~e) other than L/R"
            dir)]))
(define (tape-write t w)
  (match-define (tape before after) t)
  (match after
    [(cons h t)
     (tape before (cons w t))]
    [(list)
     (tape before (list w))]))

(struct *state (state tape))
(define (step tm s)
  (match-define (*tm _ blank final? delta) tm)
  (match-define (*state st t) s)
  (cond
    [(final? st)
     s]
    [else
     (define h (tape-read t blank))
     (define-values (n-st w dir) (delta st h))
     (define n-t (tape-write t w))
     (define nn-t (tape-move n-t blank dir))
     (*state n-st nn-t)]))

(define (step-n tm s n)
  (if (zero? n)
    s
    (step-n tm (step tm s) (sub1 n))))

(define (run tm input steps)
  (define initial-s
    (*state (*tm-initial tm) input))
  (step-n tm initial-s steps))

(module+ test
  (define busy-beaver
    (tm #:Q (A B C HALT)
        #:G (0 1)
        #:b 0
        #:S (1)
        #:q0 A
        #:F (HALT)
        #:delta
        [(A 0) -> (   B 1 R)]
        [(A 1) -> (   C 1 L)]
        [(B 0) -> (   A 1 L)]
        [(B 1) -> (   B 1 R)]
        [(C 0) -> (   B 1 L)]
        [(C 1) -> (HALT 1 R)]))

  (run busy-beaver
       empty-tape
       14))
