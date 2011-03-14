#lang racket
; Based on http://www.gamefaqs.com/psp/971508-shin-megami-tensei-persona-3-portable/faqs/60399
(require racket/runtime-path)

(define-runtime-path db-pth "p3p-db.rktd")

(define total 0)
(define unfused 0)
(define unfused/level 0)

(struct persona (arcana name base-lvl cost) #:transparent)
(printf "Special:\n")
(define db
  (with-input-from-file
      db-pth
    (λ ()
      (define max-lvl (read))
      (define inv (read))
      (for/fold ([db empty])
        ([a (in-port)])
        (match-define (cons arcana ps) a)
        (for/fold ([db db])
          ([a (in-list ps)])
          (match-define (list name base-lvl cost) a)
          (set! total (add1 total))
          (unless (number? cost)
            (when (base-lvl . <= . max-lvl)
              (set! unfused/level (add1 unfused/level)))
            (set! unfused (add1 unfused)))
          (cond
            [(base-lvl . > . max-lvl)
             db]
            [(symbol? cost)
             (printf "\t~a\n" name)
             db]
            [else
             (cons (persona arcana name base-lvl cost)
                   db)]))))))

(printf "\n~a/~a = ~a% complete\n\n" 
        (- total unfused) total
        (real->decimal-string (* 100 (/ (- total unfused) total)) 2))

(define (trim s) (regexp-replace #px"\\s+$" s ""))
(define (parse-db db)
  (for/fold ([reading? #f]
             [arcana #f]
             [combos empty])
    ([l (in-lines)])
    (match l
      ["|=======================================|"
       (values #t #f empty)]
      [" ---------------------------------------"
       (hash-set! db arcana combos)
       (values #f #f empty)]
      [_
       (if
        reading?
        (match l
          [(regexp #px"^\\|\\s+(.+)\\|\\|\\s+(.+)\\s+\\|\\s+(.+)\\s+\\|$"
                   (list _
                         (app trim note)
                         (app trim (and 1st (not "")))
                         (app trim (and 2nd (not "")))))
           (values reading?
                   (match note
                     [(or (regexp #rx"\\[.+\\]" (list _))
                          (regexp #rx"-.+-" (list _))
                          "")
                      arcana]
                     [_
                      note])
                   (list* (cons 1st 2nd) combos))]
          [_
           (values reading? arcana combos)])
        (values reading? arcana combos))]))
  (void))

(define-syntax-rule (define-db id pth)
  (begin
    (define-runtime-path db-pth pth)
    (define id (make-hash))
    (with-input-from-file db-pth (λ () (parse-db id)))))

(define-db normal-db "normal-spread.dat")
(define-db triangle-db "triangle-spread.dat")

(define arcana->personas (make-hash))
(define (arcana-personas a)
  (hash-ref! arcana->personas a
             (λ ()
               (sort 
                (filter (compose (curry string=? a)
                                 persona-arcana)
                        db)
                < #:key persona-base-lvl))))

(define (normal-fusion-lvl 1st 2nd)
  (add1
   (floor
    (/ (+ (persona-base-lvl 1st)
          (persona-base-lvl 2nd))
       2))))

(define (find-result-persona l a)
  (findf (compose (curry <= l)
                  persona-base-lvl)
         (arcana-personas a)))

(define (+* a b)
  (if (and (number? a) (number? b))
      (+ a b)
      +inf.0))

(struct fusion (cost) #:transparent)
(struct fusion:normal fusion (1st 2nd) #:transparent)

(define (normal-fusions p)
  (match-define (persona a _ _ _) p)
  (for/fold ([os empty])
    ([1*2 (in-list (hash-ref normal-db a))])
    (match-define (cons 1st-arcana 2nd-arcana) 1*2)
    (if (equal? 1st-arcana 2nd-arcana)
        os ; XXX
        (for*/fold ([os os])
          ([1st (arcana-personas 1st-arcana)]
           [2nd (arcana-personas 2nd-arcana)]
           #:when (not (equal? 1st 2nd)))
          (define cost
            (+* (persona-cost 1st)
                (persona-cost 2nd)))
          (if (and 
               (equal?
                p
                (find-result-persona (normal-fusion-lvl 1st 2nd) a))
               (not (equal? cost +inf.0)))
              (cons (fusion:normal cost 1st 2nd) os)
              os)))))

(define (triangle-fusions p)
  ; XXX
  empty)

(for ([p (in-list db)]
      #:when (not (persona-cost p)))
  (match-define (persona a name lvl _) p)
  (printf "Lvl ~a. ~a\n" lvl name)
  
  (define recipe? #f)
  (for* ([v
          (in-list
           (sort (append (normal-fusions p)
                         (triangle-fusions p))
                 < #:key fusion-cost))])
    (match v
      [(fusion:normal cost 1st 2nd)
       (set! recipe? #t)
       (printf "\t~a x ~a [~a]\n" (persona-name 1st) (persona-name 2nd) cost)]
      [#f
       (void)]))
  
  (unless recipe?
    (printf "\tUnavailable\n")))
