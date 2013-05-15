#lang racket
(require "interface.rkt")
(define-interface listy!
  [kons? (-> any/c boolean?)]
  [kons (-> any/c any/c kons?)]
  [kar (-> kons? any/c)]
  [kdr (-> kons? any/c)])
(provide listy!)
