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
     (match before
       [(cons b-hd b-tl)
        (tape b-tl (cons b-hd after))]
       [(list)
        (tape empty (cons b after))])]
    ['R
     (match after
       [(cons a-hd a-tl)
        (tape (cons a-hd before) a-tl)]
       [(list)
        (tape (cons b before) empty)])]
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

(define (step-n tm s n
                #:inform [inform-f void])
  (inform-f s)
  (cond
    [(zero? n)
     s]
    [else
     (define ns (step tm s))
     (step-n tm ns (sub1 n)
             #:inform inform-f)]))

(define (run tm input steps
             #:inform [inform-f void])
  (define initial-s
    (*state (*tm-initial tm) input))
  (step-n tm initial-s steps
          #:inform inform-f))

(require racket/format
         racket/string)
(define (display-state s)
  (match-define (*state st t) s)
  (match-define (tape before after) t)
  (printf "~a: ~a^~a\n" 
          st
          (string-append* (map ~a (reverse before)))
          (string-append* (map ~a after))))

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
       14
       #:inform display-state)

  (define addition
    (tm #:Q (0 1 2 3 4 HALT)
        #:G (* _)
        #:b _
        #:S (0)
        #:q0 0
        #:F (HALT)
        #:delta
        [(0 _) -> (0 _ R)]
        [(0 *) -> (1 * R)]
        [(1 _) -> (2 * R)]
        [(1 *) -> (1 * R)]
        [(2 _) -> (3 _ L)]
        [(2 *) -> (2 * R)]
        [(3 _) -> (3 _ L)]
        [(3 *) -> (4 _ L)]
        [(4 _) -> (HALT _ R)]
        [(4 *) -> (4 * L)]))

  (run addition
       (tape empty
             '(* * * * * _ * * * * *))
       24
       #:inform display-state))
