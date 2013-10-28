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
            (make-hasheq
             (list (cons 'final-state #t)
                   ...))
            (make-hash
             (list (cons '(delta-state . delta-symbol)
                         '(next-state write-symbol head-movement))
                   ...))))]))

(struct tape (blank before after))
(define (tape-first t)
  (match-define (tape b before after) t)
  (match after
    [(cons h _) h]
    [(list) b]))
(define (tape-rest t)
  (match-define (tape b before after) t)
  (match after
    [(cons h r) r]
    [(list) empty]))
(define (tape-tser t)
  (reverse (tape-before t)))

(define (tape-move-left t)
  (match-define (tape b before after) t)
  (match before
    [(cons b-hd b-tl)
     (tape b b-tl (cons b-hd after))]
    [(list)
     (tape b empty (cons b after))]))
(define (tape-move-right t)
  (match-define (tape b before after) t)
  (match after
    [(cons a-hd a-tl)
     (tape b (cons a-hd before) a-tl)]
    [(list)
     (tape b (cons b before) empty)]))

(define (tape-write t w)
  (match-define (tape b before after) t)
  (match after
    [(cons h t)
     (tape b before (cons w t))]
    [(list)
     (tape b before (list w))]))

(struct *state (state tape))
(define (step tm s)
  (match-define (*tm _ _ final? delta) tm)
  (match-define (*state st t) s)
  (cond
    [(hash-ref final? st #f)
     s]
    [else
     (define h (tape-first t))
     (match-define (list n-st w dir) (hash-ref delta (cons st h)))
     (define n-t (tape-write t w))
     (define nn-t
       (if (eq? 'L dir)
         (tape-move-left n-t)
         (tape-move-right n-t)))
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
  (printf "~a: ~a~a~a\n"
          st
          (string-append* (map ~a (tape-tser t)))
          (tape-first t)
          (string-append* (map ~a (tape-rest t)))))

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
       empty
       14
       #:inform display-state)

  ;; http://turingmaschine.klickagent.ch/einband/?lang=en#5_+_5
  (define addition
    (tm #:Q (0 1 2 3 4 HALT)
        #:G (* _)
        #:b _
        #:S (*)
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
       '(* * * * * _ * * * * *)
       24
       #:inform display-state))
