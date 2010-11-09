#lang racket
(require (for-syntax syntax/parse)
         "temporal.rkt"
         "automata3/re.rkt"
         "automata3/re-ext.rkt")

(define-syntax-rule (define-stx-id id)
  (define-syntax (id stx) (raise-syntax-error 'id "Used illegally" stx)))
(define-syntax-rule (define-stx-ids id ...)
  (begin (define-stx-id id) ...))

(define-stx-ids forall Pair Sum : call ret dot U)
(define-syntax (M stx)
  (syntax-parse
   stx
   [(_ K:expr T*:expr)
    (syntax/loc stx
      (let ([monitor (compile-T* T*)])
        (compile-K monitor K)))]))
(define-syntax (compile-K stx)
  (syntax-parse
   stx
   #:literals (Pair Sum : ->)
   [(_ mon (Pair K_1 K_2))
    (syntax/loc stx
      (cons/c (compile-K mon K_1)
              (compile-K mon K_2)))]
   [(_ mon (Sum K_1 K_2))
    (syntax/loc stx
      (or/c (compile-K mon K_1)
            (compile-K mon K_2)))]
   [(_ mon (: n (-> K_1 K_2)))
    (syntax/loc stx
      ; XXX Try to create real bindings
      (->t mon 'n 
           (compile-K mon K_1)
           (compile-K mon K_2)))]
   [(_ mon ?:expr)
    (syntax/loc stx
      ?)]))

(define (re->evt-predicate m)
  (define current-re m)
  (λ (evt)
    ; Projections are not in the DSL
    (if (evt:proj? evt)
        #t
        (begin
          (set! current-re (m evt))
          (re-accepting? current-re)))))

(define-for-syntax (T->re stx)
  (syntax-parse
   stx
   #:literals (call ret dot seq * not U)
   [(call n:id p:expr)
    (syntax/loc stx
      ; XXX Don't use symbols for n
      (evt:call 'n _ _ _ _ _ (list p)))]
   [(ret n:id p:expr)
    (syntax/loc stx
      ; XXX Don't use symbols for n
      (evt:return 'n _ _ _ _ _ _ (list p)))]
   ; XXX Is this "all" or any one event?
   [dot
    (syntax/loc stx
      _)]
   [(seq T_1:expr T_2:expr)
    (quasisyntax/loc stx
      (seq #,(T->re #'T_1) #,(T->re #'T_2)))]
   [(* T_1:expr)
    (quasisyntax/loc stx
      (star #,(T->re #'T_1)))]
   [(not T_1:expr)
    (quasisyntax/loc stx
      (complement #,(T->re #'T_1)))]
   [(U T_1:expr T_2:expr)
    (quasisyntax/loc stx
      (union #,(T->re #'T_1) #,(T->re #'T_2)))]))
(define-syntax (compile-T* stx)
  (syntax-parse
   stx
   #:literals (forall)
   ; XXX I don't handle quantifiers yet
   [(_ (forall () T:expr))
    (quasisyntax/loc stx
      (re->evt-predicate
       (re #,(T->re #'T))))]))

#;(define MallocFreeSpec
    (M (Pair (: malloc (-> void? addr?))
             (: free (-> addr? void?)))
       (forall (z)
               (not (seq (call free z)
                         (seq (* (not (ret malloc z)))
                              (call free z)))))))

(define addr? number?)
(define MallocFreeSpec
  (M (Pair (: malloc (-> void? addr?))
           (: free (-> addr? void?)))
     (forall ()
             (not (seq (call free _)
                       (seq (* (not (ret malloc _)))
                            (call free _)))))))


