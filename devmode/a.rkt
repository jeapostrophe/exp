#lang racket/base
(require web-server/http)

(provide start)

(define (start req)
  (response/xexpr "F"))
