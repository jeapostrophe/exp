#!/usr/bin/env racket
#lang racket/base
(require gregor
         gregor/period)

(define (pd s)
  (parse-date s "yyyy/MM/dd"))

(define (go start end)
  (displayln (period-ref (date-period-between (pd start) (pd end) '(days)) 'days)))

(module+ main
  (require racket/cmdline)
  (command-line #:program "days-between-dates"
                #:args (start end)
                (go start end)))
