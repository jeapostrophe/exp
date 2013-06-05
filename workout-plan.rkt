#lang racket/base
(require racket/file
         racket/match
         racket/list
         racket/runtime-path
         xml)

(struct e (sets reps-per-set ctxt name))
(struct a (thing new))

;; a2ps -4 ... --borders=no -o ...

(define (list->hash l)
  (for/hasheq ([k*v (in-list l)])
              (values (first k*v) (second k*v))))

(define (context-subset? ctxt last-ctxt)
  (for/or ([(k v) (in-hash ctxt)])
    (and (not (equal? v (hash-ref last-ctxt k #f)))
         (cons k v))))

(define (em e)
  `(em ,(format "~a" e)))

(define format-ctxt
  (match-lambda*
   [(list 'peg to)
    `(span "Move peg to " ,(em to))]
   [(list 'weight to)
    `(span "Move weights to " ,(em to))]
   [(list 'seat to)
    `(span "Move seat to " ,(em to))]
   [(list 'where to)
    `(span "Move to " ,(em to))]
   [(list 'bar to)
    `(span "Move bar to " ,(em to))]
   [(list 'seat-pos to)
    `(span "Move seat-pos to " ,(em to))]))

(define-runtime-path images-dir ".workout-plan")

(define (exercise-plan last-ctxt es)
  (match es
    [(list)
     (values last-ctxt empty)]
    [(list-rest (a what to) es)
     (define new-ctxt (hash-set last-ctxt what to))
     (define-values (final-ctxt rest-plan) (exercise-plan new-ctxt es))
     (values
      final-ctxt
      (cons
       (format "\\action{~a}" (format-ctxt what to))
       rest-plan))]
    [(list-rest (e sets reps-per-seat ctxt name) es)
     (cond
       [(context-subset? (list->hash ctxt) last-ctxt)
        => (λ (e) (error 'execise-plan "Context off: ~e" e))])
     (define-values (final-ctxt rest-plan) (exercise-plan last-ctxt es))
     (values
      final-ctxt
      (cons
       (format "\\exercise{~a}{~a}" 
               (format "~ax~a ~a" sets reps-per-seat name)
               (format "~a/~a.png" (path->string images-dir) name))
       rest-plan))]))

(define (draw init-ctxt p es)
  (define-values (final-ctxt x)
    (exercise-plan init-ctxt es))
  (cond
    [(context-subset? init-ctxt final-ctxt)
     => (λ (e) (error 'draw "Inconsistent start vs end: ~e" e))])  
  (with-output-to-file
      p #:exists 'replace
      (λ ()
        (for-each displayln x))))

(module+ main
  (define-runtime-path output.tex "workout-plan.tex")
  (define-runtime-path output-inner.tex "workout-plan-inner.tex")
  (define-runtime-path output.pdf "workout-plan.pdf")
  (define exercises
    (list
     (a 'where 'free)
     (e 1  50 '((where free))
        "hindu squat")
     (a 'where 'pull-up-bar:above)
     (e 1  10 '((where pull-up-bar:above))
        "wide")
     (e 1  10 '((where pull-up-bar:above))
        "narrow")
     (e 1  10 '((where pull-up-bar:above))
        "neutral")
     (a 'where 'pull-up-bar:free)
     (e 4  25 '((where pull-up-bar:free))
        "push up")
     (a 'seat-pos 'front)
     (a 'where 'gym:seated)
     (e 4 50 '((where gym:seated) (seat down))
        "crunches")
     (a 'seat 'flat)
     (e 1  25 '((where gym:seated) (seat flat))
        "leg curl")
     (e 5  10 '((where gym:seated) (seat flat) (weight back) (peg bottom))
        "lat pull")
     (a 'peg 'bottom+2)
     (a 'seat 'top-2)
     (a 'weight 'front)
     (e 5  10 '((where gym:seated) (seat top-2) (weight front) (peg bottom+2))
        "chest press")
     (a 'seat 'bot+1)
     (e 1  25 '((where gym:seated) (seat bot+1))
        "quad extension")
     (a 'peg 'top-2)
     (a 'bar 'removed)
     (e 5  10 '((where gym:seated) (seat bot+1) (weight front) (peg top-2))
        "shoulder press")
     (a 'peg 'bottom+2)
     (a 'seat 'down)
     (a 'seat-pos 'side)
     (a 'bar 'there)
     (a 'where 'gym:standing)
     (e 2  25 '((where gym:standing) (seat-pos side) (weight front) (peg bottom+2))
        "squat")
     (a 'peg 'top-1)
     (e 2  25 '((where gym:standing) (seat-pos side) (weight front) (peg top-1))
        "calf raise")
     (a 'peg 'bottom)
     (e 2  25 '((where gym:standing) (seat-pos side) (weight front) (peg bottom))
        "arm curl")
     (e 5  10 '((where gym:standing) (seat-pos side) (weight front) (peg bottom))
        "row")
     (e 2  25 '((where gym:standing) (seat-pos side) (weight front) (peg bottom))
        "shrug")
     (a 'weight 'back)
     (e 5  10 '((where gym:standing) (seat-pos side) (weight back) (peg bottom))
        "tricep press")))
  (draw (hasheq 'seat-pos 'side
                'seat 'down
                'weight 'back
                'peg 'bottom)
        output-inner.tex exercises)
  (require racket/system
           racket/path)
  (system* "/usr/bin/pdflatex" output.tex))
