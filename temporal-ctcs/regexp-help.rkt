#lang racket
(struct regex-transformer (>regex))

(provide (struct-out regex-transformer))

#|
(struct nfa (starts accepting non-accepting state->rules))

(define (nfa-complement n)
  (match-define (nfa starts accepting non-accepting state->rules) n)
  (nfa starts (list* failure non-accepting) accepting
       (list*
        (list failure (list 
        (for/list ([state*rules (in-list state->rules)])
         (match-define (list state rules))
         (list state
               (list* (list #`(not (or #,@(map first rules)))
                            (list failure))
                      rules)))
|#