#lang racket
(require (for-syntax syntax/parse unstable/syntax) racket/stxparam)
(define-syntax-parameter break
  (λ (stx) (raise-syntax-error 'break "Used outside cas-cad-e" stx)))
(define-syntax cas-cad-e
  (syntax-parser
   [(_ e:expr [opt body:expr ...+] ...)
    (with-syntax* (; Generate an identifier for each case
                   [(id ...) (generate-temporaries #'(opt ...))]
                   ; But we want them to appear in the let* in the
                   ; reverse order, because earlier cases only refer
                   ; to later cases
                   [(f ...) (reverse (syntax->list #'(id ...)))]
                   ; We want the action of each to be in the opposite
                   ; order as well
                   [((action ...) ...) (reverse (syntax->list #'((body ...) ...)))]
                   ; Each branch explicitly lists its next case, but
                   ; we use a list so that the final one can have no next
                   ; We drop the first, because the list is (add1 (length #'(id ...)))
                   ; and if we didn't, case would "drop" to themselves
                   [((next ...) ...) (reverse (cdr (syntax->list #'((id) ... ()))))])
      ; Break is handled by an escape continuation
      #'(let/ec escape
          (syntax-parameterize 
           ; We break hygeine with a pleasant syntax parameter that
           ; gets renamed to the escape continuation
           ([break (make-rename-transformer #'escape)])
           ; Each branch's functions gets put here
           (let* ([f (lambda () action ... (next) ...)] ...)
             ; We use the real case macro to do the comparisons, so
             ; we have guaranteed compatibility. That's where 'else'
             ; comes from. =)
             (case e [opt (id)] ...)))))]))

(require tests/eli-tester)

(test
 (break 3) =error> "Used outside cas-cad-e"
 
 (cas-cad-e 1 [(1)]) =error> "bad syntax"
 
 (cas-cad-e 1 [() 1]) => (void)
 
 (local [(define printed "")
         (define (cas1 v)
           (set! printed "")
           (cas-cad-e v
                      [(1) (set! printed (string-append printed "1"))]
                      [(2) (set! printed (string-append printed "2")) (break 2)]
                      [(3) 3]))]
   (test (cas1 1) => 2
         printed => "12"
         (cas1 2) => 2
         printed => "2"
         (cas1 3) => 3
         printed => ""
         (cas1 4) => (void)
         printed => ""))
 (local [(define (cas3 v)
           (let ([w true])
             (cas-cad-e v
                        [(0) (set! w false)]
                        [(1) (if w (break 1) (break 0))])))]
   (test (cas3 0) => 0
         (cas3 1) => 1))
 
 (cas-cad-e 1 [(1) (values 1 2)]) => (values 1 2)
 (cas-cad-e 1) => (void)
 (cas-cad-e 1 [(2) 3] [else 4]) => 4)