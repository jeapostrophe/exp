#lang racket/base
(require racket/local
         racket/match
         racket/set
         racket/list
         (for-syntax syntax/parse
                     racket/list
                     racket/base))

(struct dfa (next)
        #:property prop:procedure 0)
(struct dfa-accepting dfa ())

(define fail (dfa (λ (_) fail)))

(define-syntax (*dfa stx)
  (syntax-parse
   stx
   [(_ start:id
       ([state:id ([evt:expr next-state:id] ...)]
        ...)
       ([!state:id ([!evt:expr !next-state:id] ...)]
        ...))
    (syntax/loc stx
      (local
        [(define state
           (dfa-accepting 
            (match-lambda
              [evt next-state]
              ...
              [_ fail])))
         ...
         (define !state
           (dfa 
            (match-lambda
              [!evt !next-state]
              ...
              [_ fail])))
         ...]
        start))]))

(define (dfa-accepts? dfa evts)
  (if (empty? evts)
      (dfa-accepting? dfa)
      (dfa-accepts? (dfa (first evts)) (rest evts))))

(provide
 (rename-out [*dfa dfa])
 dfa?
 dfa-accepting?
 dfa-accepts?)