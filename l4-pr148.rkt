#lang racket

;; I don't understand why this doesn't work. Maybe because picosat
;; isn't guaranteeing the minimal solution?

(define var 1)
(define (amb-bool)
  (begin0 var
          (set! var (add1 var))))

(define (list-ref* l . is)
  (if (empty? is)
    l
    (apply list-ref* (list-ref l (first is)) (rest is))))

(define solve-box
  ;; Each plane (from front to back)
  (list
   ;; Plane 1 (front)
   (list
    ;; Row then column
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool)))
   ;; Plane 2 (middle)
   (list
    ;; Row then column
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool)))
   ;; Plane 3 (back)
   (list
    ;; Row then column
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool))
    (list (amb-bool) (amb-bool) (amb-bool)))))

(define check-box
  ;; Each plane (from front to back)
  (list
   ;; Plane 1 (front)
   (list
    ;; Row then column
    (list #f #f #f)
    (list #f #t #f)
    (list #f #f #f))
   ;; Plane 2 (middle)
   (list
    ;; Row then column
    (list #f #t #f)
    (list #f #t #f)
    (list #t #t #f))
   ;; Plane 3 (back)
   (list
    ;; Row then column
    (list #f #f #f)
    (list #f #f #f)
    (list #f #f #f))))

(define box solve-box)

(define clauses empty)
(define (clause! c)
  (set! clauses (cons c clauses)))

(define check-equal?
  (match-lambda*
   [(list (list (? boolean? val) ...) (? boolean? should-be))
    (unless (equal? (ormap (λ (x) x) val) should-be)
      (error 'box "Not correct"))]
   [(list (list (? number? var) ...) #t)
    (clause! var)]
   [(list (list (? number? var) ...) #f)
    (clause! (map (curry cons 'not) var))]
   [(list (? list? lhs) (? list? rhs))
    (for-each check-equal? lhs rhs)]))

(check-equal?
 ;; Top view
 (for/list ([plane (in-range 3)])
   (for/list ([col (in-range 3)])
     (for/list ([row (in-range 3)])
       (list-ref* box plane row col))))
 (list (list #f #t #f)
       (list #t #t #f)
       (list #f #f #f)))
(check-equal?
 ;; Side view
 (for/list ([row (in-range 3)])
   (for/list ([plane (in-range 3)])
     (for/list ([col (in-range 3)])
       (list-ref* box plane row col))))
 (list (list #f #t #f)
       (list #t #t #f)
       (list #f #t #f)))
(check-equal?
 ;; Front view
 (for/list ([row (in-range 3)])
   (for/list ([col (in-range 3)])
     (for/list ([plane (in-range 3)])
       (list-ref* box plane row col))))
 (list (list #f #t #f)
       (list #f #t #f)
       (list #t #t #f)))

(module+ main
  (define-values (sp stdout stdin stderr)
    (subprocess #f #f #f "/usr/bin/picosat"))

  (fprintf stdin "c p148\n")
  (fprintf stdin "p cnf ~a ~a\n" (sub1 var) (length clauses))
  (for ([c (in-list clauses)])
    (for ([v (in-list c)])
      (match v
        [(? number? n)
         (fprintf stdin "~a " n)]
        [(cons 'not (? number? n))
         (fprintf stdin "-~a " n)]))
    (fprintf stdin "0\n"))

  (close-output-port stdin)

  (subprocess-wait sp)

  (define var->val (make-hasheq))

  (let loop ([v (read stdout)])
    (match v
      ['s
       (match (read stdout)
         ['SATISFIABLE
          (loop (read stdout))])]
      ['v
       (loop (read stdout))]
      [(? number? n)
       (hash-set! var->val (abs n)
                  (not (negative? n)))
       (loop (read stdout))]
      [(? eof-object?)
       (void)]))

  (define fill-in
    (match-lambda
     [(? list? l)
      (begin0
        (for/sum ([e (in-list l)])
                 (fill-in e))
        (newline))]
     [(? number? n)
      (fill-in (hash-ref var->val n))]
     [(? boolean? b)
      (printf "~a " b)
      (if b 1 0)]))

  (printf "Total: ~a\n"
          (fill-in box)))
