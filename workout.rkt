#lang racket/base
(require racket/file
         racket/date
         racket/match
         racket/list
         racket/function
         plot)
(plot-new-window? #t)

(define data "/home/jay/Dev/scm/github.jeapostrophe/home/etc/workout.rktd")
(define data-pts (file->list data))

(define data-pt-day-abs
  (match-lambda
   [(list* year month day _)
    (find-seconds 0 0 0 day month year)]))

(define day-zero
  (data-pt-day-abs (first data-pts)))

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
(parameterize ([plot-x-ticks (date-ticks)])
  (plot
   (for/list ([(regime ds) (in-hash workout->data-series)]
              [i (in-naturals)])
     (list
      (points ds)
      (lines ds
             #:color i
             #:label (symbol->string regime))))))

(read)
