#lang racket
(require "regexp-help.rkt"
         (for-syntax syntax/parse
                     racket/list
                     racket/match
                     "regexp-help.rkt"
                     unstable/syntax))

(define-syntax-rule (define-regex-transformer id lam)
  (define-syntax id (regex-transformer lam)))

(define-syntax (epsilon stx) (raise-syntax-error 'epsilon "Outside regex" stx))
(define-syntax (complement stx) (raise-syntax-error 'complement "Outside regex" stx))
(define-syntax (seq stx) (raise-syntax-error 'seq "Outside regex" stx))
(define-syntax (union stx) (raise-syntax-error 'union "Outside regex" stx))
(define-syntax (star stx) (raise-syntax-error 'star "Outside regex" stx))

(define (fail-forever input)
  (values #f #t fail-forever))
(define (regex-or lhs-next rhs-next)
  (λ (input)
    (define-values (lhs-accepting? lhs-done? lhs-next+) (lhs-next input))
    (define-values (rhs-accepting? rhs-done? rhs-next+) (rhs-next input))
    (values (or lhs-accepting? rhs-accepting?)
            (or lhs-done? rhs-done?)
            (regex-or lhs-next+ rhs-next+))))
(define (regex-seq accepting? done? next get-after)
  (if done?
      (get-after)
      (values accepting?
              done?
              (λ (input)
                (define-values (accepting?+ done?+ next+) (next input))
                (regex-seq accepting?+ done?+ next+ get-after)))))

(define-syntax (compile-regex stx)
  (syntax-parse
   stx
   #:literals (complement seq union star epsilon)
   [(_ (complement lhs:expr))
    (raise-syntax-error 'regex "Complement not supported" stx)]
   [(_ (star lhs:expr))
    (raise-syntax-error 'regex "Star not supported" stx)
    #;(syntax/loc stx
      (let-values ([(lhs-accepting? lhs-next) (compile-regex lhs)])
        (letrec ([this (λ () (regex-seq #t lhs-next this))])
          (this))))]
   [(_ (seq lhs:expr rhs:expr))
    (syntax/loc stx
      (let-values ([(lhs-accepting? lhs-done? lhs-next) (compile-regex lhs)])
        (regex-seq lhs-accepting? lhs-done? lhs-next (λ () (compile-regex rhs)))))]
   [(_ (seq lhs:expr rest:expr ...))
    (syntax/loc stx
      (compile-regex (seq lhs (seq rest ...))))]
   [(_ (union lhs:expr rhs:expr))
    (syntax/loc stx
      (let-values ([(lhs-accepting? lhs-done? lhs-next) (compile-regex lhs)]
                   [(rhs-accepting? rhs-done? rhs-next) (compile-regex rhs)])
        (values (or lhs-accepting? rhs-accepting?)
                (or lhs-done? rhs-done?)
                (regex-or lhs-next rhs-next))))]
   [(union lhs:expr rest:expr ...)
    (syntax/loc stx
      (compile-regex (union lhs (union rest ...))))]
   [(_ (~and e (~var transformer (static regex-transformer? "regex transformer"))))
    (quasisyntax/loc stx
      (compile-regex #,((regex-transformer->regex (attribute transformer.value)) #'e)))]
   [(_ (~and e ((~var transformer (static regex-transformer? "regex transformer")) . _)))
    (quasisyntax/loc stx
      (compile-regex #,((regex-transformer->regex (attribute transformer.value)) #'e)))]
   [(_ epsilon)
    (syntax/loc stx
      (values #t #t fail-forever))]
   [(_ pat:expr)
    (syntax/loc stx
      (values #f #t
              (match-lambda [pat (values #t #t fail-forever)]
                            [_ (values #f #t fail-forever)])))]))

(define-syntax-rule (make-a-regex ce)
  (call-with-values
   (λ () ce)
   (λ (a d n) (a-regex a n))))
(define-syntax-rule (regex e)
  (make-a-regex (compile-regex e)))

(struct a-regex (accepting? advancer))
        
(define (regex-advance r i)
  (make-a-regex ((a-regex-advancer r) i)))
(define regex-accepting? a-regex-accepting?)
(define (regex-accepts? regex evts)
  (if (empty? evts)
      (regex-accepting? regex)
      (regex-accepts? (regex-advance regex (first evts)) (rest evts))))

(provide
 complement seq union star epsilon
 define-regex-transformer
 regex
 regex-advance
 regex-accepting?
 regex-accepts?)