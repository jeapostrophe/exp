#lang racket
; Based on http://www.gamefaqs.com/psp/971508-shin-megami-tensei-persona-3-portable/faqs/60399
(require racket/runtime-path)

(define-runtime-path db-pth "p3p-db.rktd")

(struct persona (arcana name base-lvl cost) #:transparent)
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
          (cons (persona arcana name base-lvl
                         (cond
                           [(base-lvl . > . max-lvl)
                            +inf.0]
                           [(member name inv)
                            0]
                           [else
                            cost]))
                db))))))

(define-runtime-path fusion-db-pth "normal-spread.dat")
(define (trim s) (regexp-replace #px"\\s+$" s ""))
(define fusion-db (make-hash))
(with-input-from-file
    fusion-db-pth
  (λ ()
    (for/fold ([reading? #f]
               [arcana #f]
               [combos empty])
      ([l (in-lines)])
      (match l
        ["|=======================================|"
         (values #t #f empty)]
        [" ---------------------------------------"
         (hash-set! fusion-db arcana combos)
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
    (void)))

(define arcana->personas (make-hash))
(define (arcana-personas a)
  (hash-ref! arcana->personas a
             (λ ()
               (sort 
                (filter (compose (curry string=? a)
                                 persona-arcana)
                        db)
                < #:key persona-base-lvl))))

(define (fuse-persona-level 1st 2nd)
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

(struct pairing (1st 2nd cost) #:transparent)

(define (find-normal-fusion p)
  (match-define (persona arcana name base-lvl cost) p)
  (define os
    (for/fold ([os empty])
      ([1*2 (in-list (hash-ref fusion-db arcana))])
      (match-define (cons 1st-arcana 2nd-arcana) 1*2)
      (for*/fold ([os os])
        ([1st (arcana-personas 1st-arcana)]
         [2nd (arcana-personas 2nd-arcana)]
         #:when (not (equal? 1st 2nd)))
        (if (equal?
             p
             (find-result-persona
              (fuse-persona-level 1st 2nd)
              arcana))
            (cons (pairing 1st 2nd
                           (+* (persona-cost 1st)
                               (persona-cost 2nd)))
                  os)
            os))))
  (if (empty? os)
      #f
      (first
       (sort os <
             #:key pairing-cost))))

(define all
  (for/list ([p (in-list db)]
             #:when (not (persona-cost p)))
    (cons p (find-normal-fusion p))))

(define all-avail
  (filter cdr all))

(define all-avail/sorted
  (sort all-avail < #:key (compose pairing-cost cdr)))

(for ([p*p (in-list all-avail/sorted)]
      [i (in-range 1 6)])
  (match-define 
   (cons 
    (persona t_arcana t_name t_base-lvl t_cost)
    (pairing 
     (persona 1_arcana 1_name 1_base-lvl 1_cost)
     (persona 2_arcana 2_name 2_base-lvl 2_cost)
     cost))
   p*p)
  (printf "~a. ~a = ~a x ~a (~a)\n"
          i t_name 1_name 2_name
          cost))
