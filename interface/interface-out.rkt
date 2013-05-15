#lang racket
(require "interface.rkt"
         "interface-def.rkt")

(struct kons (kar kdr))
(define kar kons-kar)
(define kdr kons-kdr)

(provide
 (interface-out listy!))
