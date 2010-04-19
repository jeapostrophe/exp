#lang scheme

(define-syntax-rule (automaton
                     start-state
                     [state (pat next-state)
                            ...]
                     ...
                     (end-state ...))
  (lambda (seq)
    (define-values (non-empty-seq? next-element) (sequence-generate seq))
    (define (state)
      (if (non-empty-seq?)
          (match (next-element)
            [pat (next-state)]
            ...)
          (handle-end state)))
    ...
    (define (handle-end the-end-state)
      (or (eq? the-end-state end-state)
          ...))
    (start-state)))

(define cadr-maton
  (automaton start
             [start ('c more)]
             [more ('a more)
                   ('d more)
                   ('r end)]
             [end]
             (end)))

(cadr-maton (in-list '(c a d r)))
(cadr-maton (in-port read (current-input-port)))