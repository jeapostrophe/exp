#lang racket/base
(require (for-syntax racket/base
                     syntax/parse)
         racket/function
         racket/match
         racket/list)

(define-syntax-rule (define-check id S)
  (define (id s)
    (if (memq s S)
      s
      (error 'id "~e" s))))
(define-check check-LR '(L R))

(struct *tm (initial states inputs blank final? delta))
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
         (next-state write-symbol head-movement)]
        ...)
     (syntax/loc stx
       (let ()
         (define-check check-G '(sym ...))
         (define-check check-Q '(state ...))
         (*tm (check-Q 'initial-state)
              '(state ...)
              ;; Why should the blank not be included?
              (list (check-G 'input) ... (check-G 'blank))
              (check-G 'blank)
              (make-hasheq
               (list (cons (check-Q 'final-state) #t)
                     ...))
              (make-hash
               (list (cons (cons (check-Q 'delta-state)
                                 (check-G 'delta-symbol))
                           (list (check-Q 'next-state)
                                 (check-G 'write-symbol)
                                 (check-LR 'head-movement)))
                     ...)))))]))

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
  (match-define (*tm _ _ _ _ final? delta) tm)
  (match-define (*state st t) s)
  (cond
    [(hash-ref final? st #f)
     s]
    [else
     (define h (tape-first t))
     (match-define
      (list n-st w dir)
      (hash-ref delta (cons st h)
                (λ ()
                  (error 'step "No transition defined for ~v in ~v state"
                         h st))))
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
  (define (valid-input? s)
    (memq s (*tm-inputs tm)))
  (for ([s (in-list input)])
    (unless (valid-input? s)
      (error 'run "Invalid input: ~e" s)))

  (define initial-s
    (*state
     (*tm-initial tm)
     (tape (*tm-blank tm)
           empty
           input)))
  (step-n tm initial-s steps
          #:inform inform-f))

(require racket/format
         racket/string)
(define (make-display-state tm)
  (define max-st-len
    (apply max
           (map (compose string-length symbol->string)
                (*tm-states tm))))
  (λ (s)
    (match-define (*state st t) s)
    (displayln
     (~a (~a #:min-width max-st-len st) ": "
         (string-append* (map ~a (tape-tser t)))
         "[" (tape-first t) "]"
         (string-append* (map ~a (tape-rest t)))))))

(module+ test
  (define busy-beaver
    (tm #:Q (A B C HALT)
        #:G (0 1)
        #:b 0
        #:S (1)
        #:q0 A
        #:F (HALT)
        #:delta
        [(A 0) (   B 1 R)]
        [(A 1) (   C 1 L)]
        [(B 0) (   A 1 L)]
        [(B 1) (   B 1 R)]
        [(C 0) (   B 1 L)]
        [(C 1) (HALT 1 R)]))

  (run busy-beaver
       empty
       14
       #:inform (make-display-state busy-beaver))

  ;; http://turingmaschine.klickagent.ch/einband/?lang=en#5_+_5
  (define addition
    (tm #:Q (consume-first-number
             consume-second-number
             override-last-*
             seek-beginning
             HALT)
        #:G (* _ /)
        #:b _
        #:S (* /)
        #:q0 consume-first-number
        #:F (HALT)
        #:delta
        [(consume-first-number *)
         (consume-first-number * R)]
        [(consume-first-number /)
         (consume-second-number * R)]
        [(consume-second-number *)
         (consume-second-number * R)]
        [(consume-second-number _)
         (override-last-* _ L)]
        [(override-last-* *)
         (seek-beginning _ L)]
        [(seek-beginning *)
         (seek-beginning * L)]
        [(seek-beginning _)
         (HALT _ R)]))

  (run addition
       '(* * * * * / * * * * *)
       24
       #:inform (make-display-state addition))

  (define addition-program
    (tm-program
     [consume-first-number
      [* (consume-first-number * R)]
      [/ (consume-second-number * R)]]
     [consume-second-number
      [* (consume-second-number * R)]
      [_ (override-last-* _ L)]]
     [override-last-*
      [* (seek-beginning _ L)]]
     [seek-beginning
      [* (seek-beginning * L)]
      [_ (HALT _ R)]])))
