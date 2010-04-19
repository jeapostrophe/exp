#lang scheme
(require (for-syntax scheme
                     scheme/set)
         tests/eli-tester)

(define-for-syntax (identifier->number stx)
  (match (symbol->string (syntax->datum stx))
    ["_..."
     +inf.0]
    [(regexp #rx"^_(.+)$" (list _ n-as-string))
     (define n (string->number n-as-string))
     (if (number? n)
         n
         (string->keyword n-as-string))]
    [_ #f]))

; scut-finder : stx -> (list var ...)
(define-for-syntax (scut-finder stx)
  ; loop : stx -> (list (cons number identifier) ...))
  (define (loop stx)
    (syntax-case stx ()
      [x (identifier? #'x)
         (cond [(identifier->number #'x)
                => (lambda (n) (list (cons n #'x)))]
               [else
                empty])]
      [(f . r)
       (append (loop #'f) (loop #'r))]
      [x empty]))
  (define-values (lowest-n kws formals)
    (for/fold ([lowest-n +inf.0]
               [kws (set)]
               [formals empty])
      ([e (in-list (sort (loop stx)
                         >=
                         #:key 
                         (match-lambda
                           [(cons (? number? n) _)
                            n]
                           [_
                            0])))])
      (match-define (cons n id) e)
      (cond
        [(equal? n +inf.0)
         (values n kws id)]
        [(keyword? n)
         (if (set-member? kws n)
             (values lowest-n kws formals)
             (values lowest-n (set-add kws n) (list* n id formals)))]
        [(= n lowest-n)
         (values lowest-n kws formals)]
        [else
         (local 
           [(define new-lowest (min n lowest-n))
            (define missing-args
              (if (equal? lowest-n +inf.0)
                  empty
                  (for/list ([i (in-range (add1 new-lowest) lowest-n)])
                    (first (generate-temporaries (list i))))))]
           (values new-lowest kws
                   (list* id (append missing-args formals))))])))
  formals)

(define-syntax (scut* stx)
  (syntax-case stx ()
    [(_ . e)
     (with-syntax
         ([formals (scut-finder #'e)])           
       (syntax/loc stx
         (lambda formals e)))]))

(define-syntax (scut stx)
  (syntax-case stx ()
    [(_ e)
     (syntax/loc stx
       (scut* . e))]))

(test
 (let ([_a 2])
   ((scut* / _0 _a) 1 #:a 2))
 => 1/2
 
 ((scut* / _0 _1) 1 2) => 1/2
 ((scut* / _1 _0) 1 2) => 2
 ((scut* / _0 _0) 1) => 1
 ((scut* / _0 _2) 1 2 3) => 1/3
 ((scut* / _0 _2) 1 2) =error> "3 arguments"
 ((scut* / _0 _0) 1 2) =error> "1 argument"
 
 ((scut (+))) => 0
 ((scut* +)) => 0
 ((scut +)) => +
 
 ((scut _0) 1) => 1
 
 ((scut (+ _0 (/ _1 _2)))
  1 2 3) 
 => (+ 1 (/ 2 3))
 
 ((scut (+ _lhs _rhs)) #:lhs 1 #:rhs 2)
 => 3
 ((scut (+ _lhs _rhs)) #:rhs 2 #:lhs 1)
 => 3
 
 ((scut (+ _lhs _lhs _rhs)) #:lhs 1 #:rhs 2)
 => 4
 
 ((scut (apply + _0 _...))
  1 2 3)
 => 6
 
 )