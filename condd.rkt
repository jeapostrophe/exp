#lang racket/base
(require (for-syntax racket/base
                     syntax/parse))

(define-syntax (condd stx)
  (syntax-parse stx
    #:literals (define else)
    [(_)
     #'(void)]
    [(_ [else . d])
     #'(let () . d)]
    [(_ (define . d) ...+ . more)
     #'(let ()
         (define . d) ...
         (condd . more))]
    [(_ [test . b] . more)
     #'(if test
         (let () . b)
         (condd . more))]))

(condd)

(condd
 [else 1])

(condd
 (define first 1))

(condd
 [#t 1])

(condd
 (define first 1)
 [(= first 2)
  (printf "2\n")]
 (define first 2)
 [(= first 2)
  (printf "2 again\n")]
 [else
  (printf "Nope\n")])
