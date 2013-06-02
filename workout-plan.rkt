#lang racket/base
(require racket/file
         racket/match
         racket/list
         xml)
(struct e (sets reps-per-set ctxt name))

(define (ctxt-merge old new)
  (for/fold ([changes empty]
             [next old])
      ([k*v (in-list new)])
    (match-define (list k v) k*v)
    (define ov (hash-ref next k #f))
    (cond
      [(and ov (equal? ov v))
       (values changes next)]
      [else
       (values (list* (list k ov v) changes)
               (hash-set next k v))])))

(define (em e)
  `(em ,(format "~a" e)))

(define format-ctxt
  (match-lambda*
   [(list 'peg _ to)
    `(span "Move peg to " ,(em to))]
   [(list 'weight _ to)
    `(span "Move weights to " ,(em to))]
   [(list 'seat _ to)
    `(span "Move seat to " ,(em to))]
   [(list 'where _ to)
    `(span "Move to " ,(em to))]))

(define (exercise-plan last-ctxt es)
  (match es
    [(list)
     (values last-ctxt empty)]
    [(list-rest (e sets reps-per-seat ctxt name) es)
     (define-values (changes new-ctxt) (ctxt-merge last-ctxt ctxt))
     (define-values (final-ctxt rest-plan) (exercise-plan new-ctxt es))
     (values
      final-ctxt
      (append
       (for/list ([c (in-list changes)])
         (match-define (list what from to) c)
         `(tr ([class "action"])
              (td ([colspan "3"])
                  ,(format-ctxt what from to))))
       (list `(tr ([class "exercise"])
                  (td ,(number->string sets))
                  (td ,(number->string reps-per-seat))
                  (td ,name)))
       rest-plan))]))

(define (draw p es)
  (define-values (final-ctxt1 x1)
    (exercise-plan (hasheq) es))
  (define-values (final-ctxt2 x2)
    (exercise-plan (hash-set final-ctxt1 'where 'free) es))
  (unless (equal? final-ctxt1 final-ctxt2)
    (error 'draw "Inconsistent states"))
  (define x
    `(html
      (body
       (table
        ,@x2))))
  (display-to-file (xexpr->string x) p #:exists 'replace))

(module+ main
  (require racket/runtime-path)
  (define-runtime-path output.html "workout-plan.html")
  (define exercises
    (list
     (e 1  50 '((where free))
        "hindu squat")
     (e 1  10 '((where pull-up-bar:above))
        "wide")
     (e 1  10 '((where pull-up-bar:above))
        "narrow")
     (e 1  10 '((where pull-up-bar:above))
        "neutral")
     (e 4  25 '((where pull-up-bar:free))
        "push up")
     (e 4 100 '((where gym:seated) (seat down))
        "crunches")
     (e 1  25 '((where gym:seated) (seat flat))
        "leg curl")
     (e 5  10 '((where gym:seated) (seat flat) (weight back) (peg bottom))
        "lat pull")
     (e 5  10 '((where gym:seated) (seat incline) (weight front) (peg bottom+1))
        "chest press")
     (e 1  25 '((where gym:seated) (seat straight))
        "quad extension")
     (e 5  10 '((where gym:seated) (seat straight) (weight front) (peg top-2))
        "shoulder press")
     (e 5  10 '((where gym:standing) (seat side) (weight front) (peg bottom+2))
        "squat")
     (e 5  10 '((where gym:standing) (seat side) (weight front) (peg bottom+2))
        "calf raise")
     (e 5  10 '((where gym:standing) (seat side) (weight front) (peg gone))
        "arm curl")
     (e 5  10 '((where gym:standing) (seat side) (weight front) (peg gone))
        "row")
     (e 5  10 '((where gym:standing) (seat side) (weight front) (peg gone))
        "shrug")
     (e 5  10 '((where gym:standing) (seat side) (weight back) (peg bottom))
        "tricep press")))
  (draw output.html exercises))
