#lang racket/base
(require syntax/stx
         racket/list
         racket/function
         racket/match)

(define (atom-union new old)
  new)

(define flows (make-hash))
(define flow-mt (hasheq))
(define (flow-union x y)
  (for/fold
      ([x x])
      ([(ky vy) (in-hash y)])
    (if (hash-has-key? x ky)
      (hash-update x ky (curry atom-union vy))
      (hash-set x ky vy))))

(define flow-funs empty)
(struct flow-fun (pred fun))

(define (flow stx)
  (let loop ([last (hash-ref flows stx flow-mt)]
             [l flow-funs])
    (if (empty? l)
      last
      (loop (if ((flow-fun-pred (first l)) stx)
              (flow-union
               last
               ((flow-fun-fun (first l)) stx))
              last)
            (rest l)))))

(define-syntax-rule (define-flow/id id fun)
  (set! flow-funs
        (cons (flow-fun (λ (stx)
                          (and (stx-list? stx)
                               (bound-identifier=? (stx-car stx) #'id)))
                        fun)
              flow-funs)))

(define (flow-attr stx k dv)
  (hash-ref (flow stx) k (λ () dv)))

;;;;;;;;;;;;;;;;;;;;

(define (list-lift f l1 l2)
  (for*/list ([e1 (in-list l1)]
              [e2 (in-list l2)])
    (f e1 e2)))

(define-flow/id begin
  (λ (stx)
    (syntax-case stx ()
      [(_ e_0 ... e_end)
       (hasheq 'value (flow-attr #'e_end 'value empty))])))

(define-flow/id *
  (λ (stx)
    (syntax-case stx ()
      [(_ lhs rhs)
       (hasheq 'value
               (list-lift +
                          (flow-attr #'lhs 'value empty)
                          (flow-attr #'lhs 'value empty)))])))

(define example
  #'(begin
      (define (fac n)
        (cond
          [(zero? n)
           1]
          [else
           (* n (fac (sub1 n)))]))
      (fac 10)
      (* 10 5)))

(flow example)
