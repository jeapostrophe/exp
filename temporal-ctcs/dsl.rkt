#lang racket/base
(require racket/match
         racket/stxparam
         (for-syntax racket/base
                     syntax/parse
                     unstable/syntax)
         "temporal.rkt"
         "automata3/re.rkt"
         "automata3/re-ext.rkt")
(provide forall call ret
         M n->
         (all-from-out 
          "automata3/re.rkt"
          "automata3/re-ext.rkt"))

(define-syntax-rule (define-stx-id id)
  (define-syntax (id stx) (raise-syntax-error 'id "Used illegally" stx)))

(define-stx-id forall)

(define-syntax-parameter stx-monitor-id (λ (stx) (raise-syntax-error 'n-> "Used outside M" stx)))

(define-syntax (n-> stx)
  (syntax-parse
   stx
   [(_ n:id K_1 ... K_2)
    (syntax/loc stx
      (->t stx-monitor-id 'n K_1 ... K_2))]))

(define-syntax (M stx)
  (syntax-parse
   stx
   [(_ K:expr T*:expr)
    (with-syntax ([monitor (generate-temporary 'monitor)])
      (syntax/loc stx
        (let ([monitor (compile-T* T*)])
          (syntax-parameterize ([stx-monitor-id (make-rename-transformer #'monitor)])
                               K))))]))

(define (re->evt-predicate m)
  (define current-re m)
  (λ (evt)
    ; Projections are not in the DSL
    (if (evt:proj? evt)
        #t
        (begin
          (printf "~S\n" evt)
          (set! current-re (current-re evt))
          (re-accepting? current-re)))))

(define-re-transformer call
  (λ (stx)
    (syntax-parse
     stx
     [(call n:id p:expr ...)
      (syntax/loc stx
        (evt:call 'n _ _ _ _ _ (list p ...)))])))
(define-re-transformer ret
  (λ (stx)
    (syntax-parse
     stx
     [(ret n:id p:expr ...)
      (syntax/loc stx
        (evt:return 'n _ _ _ _ _ _ (list p ...)))])))

(define-syntax (compile-T* stx)
  (with-disappeared-uses
      (syntax-parse
       stx
       #:literals (forall)
       ; XXX I don't handle quantifiers yet
       [(_ ((~and f forall) () T:expr))
        (record-disappeared-uses (list #'f))
        (quasisyntax/loc stx
          (re->evt-predicate
           (re T)))])))



