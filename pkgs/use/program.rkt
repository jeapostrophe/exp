#lang s-exp "../core/racket-with-pkgs.rkt"
; XXX Notice that this uses ()s around racket/listy
;     This would be solved by "id-require-transformers" or a more cooperative require
(require rackunit (racket/listy))

(check-equal? (every-other (list 1 2 3 4))
              (list 1 3))