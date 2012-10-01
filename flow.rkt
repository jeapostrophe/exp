#lang racket/base
(require syntax/stx
         racket/list
         unstable/syntax
         racket/function
         racket/match)

(define (atom-union new old)
  new)

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

;; XXX my redo stuff doesn't really work, it should use equal? between init and next
(define flows (make-hash))
(define (flow stx)
  (define (round init)
    (let loop ([last init]
               [l flow-funs])
      (cond
        [(empty? l)
         last]
        [(memf 
          (λ (x)
            (equal? stx (car x)))
          (rest 
           (continuation-mark-set->list (current-continuation-marks) 'flowing)))
         =>
         (λ (after)
           (for-each (λ (x) (set-box! (cdr x) #t)) after)
           last)]   
        [else
         (loop (if ((flow-fun-pred (first l)) stx)
                 (flow-union
                  last
                  ((flow-fun-fun (first l)) stx))
                 last)
               (rest l))])))
  (let loop ([i 2]
             [init (hash-ref flows stx flow-mt)])
    (define redo-box (box #f))
    (define next 
      (with-continuation-mark 'flowing (cons stx redo-box)
                              (round init)))
    ;;(printf "[~a] ~a -> ~a\n" i init next)
    (hash-set! flows stx next)
    (if (or (<= i 0) (not (unbox redo-box)))
      next
      (loop (sub1 i) next))))

(define-syntax-rule (define-flow pred fun)
  (set! flow-funs
        (cons (flow-fun pred
                        fun)
              flow-funs)))

(define-syntax-rule (define-flow/id id fun)
  (define-flow (λ (stx)
                 (and (stx-list? stx)
                      (bound-identifier=? (stx-car stx) #'id)))
    fun))

(define (flow-attr stx k dv)
  (hash-ref (flow stx) k (λ () dv)))

;;;;;;;;;;;;;;;;;;;;

(define (list-lift f l1 l2)
  (remove-duplicates
   (for*/list ([e1 (in-list l1)]
               [e2 (in-list l2)])
     (f e1 e2))))

(define (all-but-last l)
  (if (empty? l)
    empty
    (reverse (rest (reverse l)))))

(define-flow/id begin
  (λ (stx)
    (syntax-case stx ()
      [(_ e_0 ... e_end)
       (hasheq 'value (flow-attr #'e_end 'value empty)
               'value-stx
               #`(begin 
                   ;; XXX this should drop the last thing
                   #,@(flow-attr stx 'effect-stxs empty)
                   #,(flow-attr #'e_end 'value-stx #f)))])))

(define-flow/id begin
  (λ (stx)
    (syntax-case stx ()
      [(_ e_0 ... e_end)
       (hasheq 'effect-stxs
               (append-map (λ (x) (flow-attr x 'effect-stxs empty))
                           (syntax->list #'(e_0 ... e_end))))])))

(define-flow/id *
  (λ (stx)
    (syntax-case stx ()
      [(_ lhs rhs)
       (hasheq 'value
               (list-lift *
                          (flow-attr #'lhs 'value empty)
                          (flow-attr #'rhs 'value empty))
               'effect-stxs
               (append (flow-attr #'lhs 'effect-stxs empty)
                       (flow-attr #'rhs 'effect-stxs empty))
               'value-stx
               #`(* #,(flow-attr #'lhs 'value-stx #f)
                    #,(flow-attr #'rhs 'value-stx #f)))])))

(define-flow/id set!
  (λ (stx)
    (syntax-case stx ()
      [(_ id rhs)
       (hasheq 'value
               (list (void))
               'effect-stxs
               (list stx)
               'value-stx
               #'stx)])))

(define-flow
  (λ (stx)
    (number? (syntax->datum stx)))
  (λ (stx)
    (hasheq 'value (list (syntax->datum stx))
            'effect-stxs '()
            'value-stx stx)))

(module+ test
  (require rackunit)
  (check-equal?
   (hash-ref
    (flow
     #'(begin
         (* 10 5)))
    'value)
   (list 50))

  (check-equal?
   (syntax->datum
    (hash-ref
     (flow
      #'(begin
          (* 10 5)
          (* 10 5)))
     'value-stx))
   '(begin (* 10 5)))

  (check-equal?
   (syntax->datum
    (hash-ref
     (flow
      #'(begin
          (* (begin (set! x 5) 10) 5)
          (* 10 5)))
     'value-stx))
   '(begin (set! x 5) (* 10 5))))
