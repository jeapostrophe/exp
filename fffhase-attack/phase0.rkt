#lang racket/base
(require "lib.rkt"
         "phase1.rkt")

(macro)
(printf "dynamic: unsafe-global is ~a\n" (unsafe-global))
(printf "dynamic: safe-global is ~a\n" (safe-global))
