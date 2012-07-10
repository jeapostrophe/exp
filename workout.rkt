#lang slideshow
(require racket/file
         racket/date
         racket/match
         racket/list
         racket/function
         plot)

(define data "/home/jay/Dev/scm/github.jeapostrophe/home/etc/workout.rktd")
(define data-pts (file->list data))

(define data-pt-day-abs
  (match-lambda
   [(list* year month day _)
    (find-seconds 0 0 0 day month year)]))

(define day-zero
  (data-pt-day-abs (first data-pts)))
(define day-last
  (data-pt-day-abs (last data-pts)))

(define (data-pt-day-rel dp)
  (/ (- (data-pt-day-abs dp) day-zero)
     (* 60 60 24)))

(define workout->data-series
  (for*/fold ([w->d (hasheq)])
      ([dp (in-list data-pts)]
       [wo (in-list (list-tail dp 3))])
    (define day (data-pt-day-abs dp))
    (match-define (list* regime numbers) wo)
    (hash-update w->d regime (curry cons (vector day (apply * numbers))) empty)))

(require racket/math)

(plot-font-size (current-font-size))
(plot-width (current-para-width))
(plot-height 600)
(plot-background-alpha 1/2)

(parameterize ([plot-x-ticks (date-ticks)])
  (for ([(regime ds) (in-hash workout->data-series)]
        [i (in-naturals)])
    (slide
     #:title (symbol->string regime)
     (plot-pict
      #:y-label
      (match regime
        [(or 'crunches 'pushups)
         "how many"]
        ['walking
         "miles"]
        [(or 'bicep 'shoulder-press 'bench 'hindu-squats 'weight)
         "pounds"])
      #:x-label "day"
      #:x-min day-zero
      #:x-max day-last
      #:y-min 0
      #:y-max (* 1.25 (apply max (map (λ (v) (vector-ref v 1)) ds)))
      (list
       (points ds)
       (lines ds
              #:color i))))))
