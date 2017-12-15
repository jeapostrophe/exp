#lang at-exp racket/base
(require (for-syntax racket/base
                     syntax/parse))

(define-syntax (2d stx)
  (syntax-parse stx
    [(_ m . body)
     (syntax/loc stx
       (m 'body))]))

@2d[quote]{
| a | b | c | d | e |
|---+---+---+---+---|
| 0 | 1 | 2 | 3 | 4 |
| 5 | 6 | 7 | 8 | 9 |
|   |   |   |   |   |
}


