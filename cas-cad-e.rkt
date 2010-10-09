#lang racket
(require (for-syntax syntax/parse unstable/syntax) racket/stxparam)
(define-syntax-parameter break
  (λ (stx) (raise-syntax-error 'break "Used outside cas-cad-e" stx)))
(define-syntax cas-cad-e
  (syntax-parser
   [(_ e:expr [opt body:expr ...+] ...)
    (with-syntax* ([(id ...) (generate-temporaries #'(opt ...))]
                   [(f ...) (reverse (syntax->list #'(id ...)))]
                   [(action ...) (reverse (syntax->list #'((begin body ...) ...)))]
                   [((next ...) ...) (reverse (cdr (syntax->list #'(((id)) ... ()))))])
      #'(let/ec escape
          (syntax-parameterize 
           ([break (make-rename-transformer #'escape)])
           (let* ([f (lambda () (void) action next ...)] ...)
             (case e [opt (id)] ...)))))]))
#;(define-syntax cas-cad-e
    (syntax-rules ()
      [(_ e) (begin e (void))]
      [(_ e [(n ...) code ...] ... [(n_l ...) code_l ...])
       (let/ec esc
         (syntax-parameterize 
          ([break (make-rename-transformer #'esc)])
          (let* ([tmp e]
                 [earlier? #f]
                 [earlier? 
                  (if (or earlier? (eqv? tmp 'n) ...)
                      (begin code ... #t)
                      earlier?)]
                 ...)
            (when (or earlier? (eqv? tmp 'n_l) ...)
              code_l ...))))]))

(require tests/eli-tester)

(define printed "")
(define (cas1 v)
  (set! printed "")
  (cas-cad-e v
             [(1) (set! printed (string-append printed "1"))]
             [(2) (set! printed (string-append printed "2")) (break 2)]
             [(3) 3]))

(test (cas1 1) => 2
      printed => "12"
      (cas1 2) => 2
      printed => "2"
      (cas1 3) => 3
      printed => ""
      (cas1 4) => (void)
      printed => "")

(define (cas3 v)
  (let ([w true])
    (cas-cad-e v
               [(0) (set! w false)]
               [(1) (if w (break 1) (break 0))])))

(test (cas3 0) => 0
      (cas3 1) => 1)

(test (cas-cad-e 1 [(1) (values 1 2)]) => (values 1 2)
      (cas-cad-e 1) => (void)
      (cas-cad-e 1 [(2) 3] [else 4]) => 4)