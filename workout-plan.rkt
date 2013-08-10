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

(define format-to
  (match-lambda*
   [(list 'weight 'back) "Move weights to rear"]
   [(list 'weight 'legs) "Move weights to legs"]
   [(list 'weight 'front) "Move weights to front"]
   [(list 'peg to) (format "Move peg to ~a" to)]
   [(list 'seat to) (format "Move seat to ~a" to)]
   [(list 'bar 'there) "Return bar"]
   [(list 'bar 'removed) "Move bar to side"]
   [(list 'seat-pos 'side) "Move base to side"]
   [(list 'seat-pos 'front) "Move base to front"]
   [(list 'where 'gym:standing) "Move to standing"]
   [(list 'where 'gym:seated) "Move to seated"]
   [(list 'where 'pull-up-bar:free) "Move to bar on floor"]
   [(list 'where 'pull-up-bar:above) "Move to bar on door"]
   [(list 'where 'free) "Move to floor"]))

(define-runtime-path images-dir ".workout-plan")

(define (exercise-plan last-ctxt es)
  (match es
    [(list)
     (values last-ctxt empty)]
    [(list-rest (? string? m) es)
     (define-values (final-ctxt rest-plan) (exercise-plan last-ctxt es))
     (values
      final-ctxt
      (cons
       (format "\\action{~a}" m)
       rest-plan))]
    [(list-rest (a what to) es)
     (define new-ctxt (hash-set last-ctxt what to))
     (define-values (final-ctxt rest-plan) (exercise-plan new-ctxt es))
     (values
      final-ctxt
      (cons
       (format "\\action{~a}" (format-to what to))
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
    [(context-subset? init-ctxt (hash-set final-ctxt 'where 'free))
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
     (e 1  50 '()
        "hindu squat")
     (e 1  10 '()
        "wide")
     (e 1  10 '()
        "narrow")
     (e 1  10 '()
        "neutral")
     (e 5  10 '()
        "push up")
     (e 5  20 '( (seat down))
        "crunches")
     (a 'seat-pos 'front)
     (a 'bar 'removed)
     (a 'weight 'legs)
     (a 'seat 'bot+1)
     (e 1  25 '((seat bot+1) (weight legs))
        "quad extension")
     (a 'seat 'flat)
     (e 1  25 '((seat flat) (weight legs))
        "leg curl")
     (a 'weight 'back)
     (e 5  10 '((seat flat) (weight back) (peg bottom))
        "lat pull")
     (a 'peg 'bottom+2)
     (a 'seat 'top-2)
     (a 'weight 'front)
     (e 5  10 '((seat top-2) (weight front) (peg bottom+2))
        "chest press")     
     (a 'peg 'top-2)
     (a 'seat 'bot+1)
     (e 5  10 '((seat bot+1) (weight front) (peg top-2))
        "shoulder press")
     (a 'seat 'down)
     (a 'peg 'bottom+2)
     (a 'seat-pos 'side)
     (a 'bar 'there)
     (e 2  25 '((seat-pos side) (weight front) (peg bottom+2))
        "squat")
     (a 'peg 'top-1)
     (e 2  25 '((seat-pos side) (weight front) (peg top-1))
        "calf raise")
     (a 'peg 'bottom)
     (e 5  10 '((seat-pos side) (weight front) (peg bottom))
        "arm curl")
     (e 5  10 '((seat-pos side) (weight front) (peg bottom))
        "row")
     (e 5  10 '((seat-pos side) (weight front) (peg bottom))
        "shrug")
     (a 'weight 'back)     
     (e 5  10 '((seat-pos side) (weight back) (peg bottom))
        "tricep press")
     "Congraturations!"))
  (draw (hasheq 'seat-pos 'side
                'seat 'down
                'where 'free
                'weight 'back
                'peg 'bottom)
        output-inner.tex exercises)
  (require racket/system
           racket/path)
  (system* "/usr/bin/pdflatex" output.tex))
