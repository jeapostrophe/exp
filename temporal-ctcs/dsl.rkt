#lang racket
(require unstable/match
         (for-syntax syntax/parse
                     syntax/id-table
                     racket/dict
                     unstable/syntax)
         "temporal.rkt"
         "automata3/re.rkt"
         "automata3/re-ext.rkt")

(define-syntax-rule (define-stx-id id)
  (define-syntax (id stx) (raise-syntax-error 'id "Used illegally" stx)))
(define-syntax-rule (define-stx-ids id ...)
  (begin (define-stx-id id) ...))

(define-stx-ids forall Pair Sum :)

; XXX Make this a normal contract macro that communicates
;     with syntax parameters, so I don't need Pair or Sum
(define-for-syntax (compile-K binds mon stx)
  (with-disappeared-uses
      (syntax-parse
       stx
       #:literals (Pair Sum : ->)
       [((~and p Pair) K_1 K_2)
        (record-disappeared-uses (list #'p))
        (quasisyntax/loc stx
          (cons/c #,(compile-K binds mon #'K_1)
                  #,(compile-K binds mon #'K_2)))]
       [((~and s Sum) K_1 K_2)
        (record-disappeared-uses (list #'s))
        (quasisyntax/loc stx
          (or/c #,(compile-K binds mon #'K_1)
                #,(compile-K binds mon #'K_2)))]
       [((~and c :) n ((~and a ->) K_1 K_2))
        (record-disappeared-uses (list #'c #'a))
        (dict-set! binds #'n #t)
        (quasisyntax/loc stx
          (->t #,mon n 
               #,(compile-K binds mon #'K_1)
               #,(compile-K binds mon #'K_2)))]
       [?:expr
        (syntax/loc stx
          ?)])))

(define-syntax (M stx)
  (syntax-parse
   stx
   [(_ K:expr T*:expr)
    (with-syntax ([monitor (generate-temporary 'monitor)])
      (define binds (make-bound-id-table))
      (define ctc (compile-K binds #'monitor #'K))
      (quasisyntax/loc stx
        (let (#,@(for/list ([n (in-dict-keys binds)])
                   (quasisyntax/loc n
                     [#,n '#,(generate-temporary n)])))
          (let ([monitor (compile-T* T*)])
            #,ctc))))]))

(define (re->evt-predicate m)
  (define current-re m)
  (λ (evt)
    ; Projections are not in the DSL
    (if (evt:proj? evt)
        #t
        (begin
          (set! current-re (m evt))
          (re-accepting? current-re)))))

(define-re-transformer call
  (λ (stx)
    (syntax-parse
     stx
     [(call n:id p:expr)
      (syntax/loc stx
        (evt:call (== n) _ _ _ _ _ (list p)))])))
(define-re-transformer ret
  (λ (stx)
    (syntax-parse
     stx
     [(ret n:id p:expr)
      (syntax/loc stx
        (evt:return (== n) _ _ _ _ _ _ (list p)))])))

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
             (complement (seq (call free _)
                              (seq (star (complement (ret malloc _)))
                                   (call free _)))))))


