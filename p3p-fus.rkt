#lang racket
(require racket/runtime-path
         unstable/markparam)

(define-runtime-path db-pth "persona_3_fusion.txt")
(define db (make-hash))

(struct entry (cost level recipes notes)
        #:mutable
        #:transparent)

(define (trim s)
  (regexp-replace #px"\\s+$" s ""))

(define (add-info! p i)
  (hash-update! db p
                (λ (e)
                  (match i
                    [(regexp #rx"^\\((.+)\\)$" (list _ note))
                     (struct-copy entry e
                                  [notes (cons note (entry-notes e))])]
                    [_
                     (struct-copy entry e
                                  [recipes (cons (regexp-split #rx" x " i) (entry-recipes e))])]))))

(with-input-from-file db-pth
  (λ ()
    (void
     (for/fold ([last #f])
       ([l (in-lines)])
       (match l
         [(regexp #px"^\\|\\s+Lv (..)\\. (.+)\\s+\\| (.+)\\s+\\|$"
                  (list _ (app string->number lvl) (app trim persona) (app trim info)))
          (hash-set! db persona
                     (entry #f lvl empty empty))
          (add-info! persona info)
          persona]
         [(regexp #px"^\\|\\s+\\| (.+)\\s+\\|$"
                  (list _ (app trim more-info)))
          (add-info! last more-info)
          last])))))

(define cycle-detect (mark-parameter))
(define computed? #f)
(define (compute-cost! p)
  (define e (hash-ref db p))
  (match-define (entry cost lvl rs _) e)
  (or cost
      (if (member p (mark-parameter-all cycle-detect))
          (begin
            #;(printf "~a appears in ~a\n" p (mark-parameter-all cycle-detect))
            +inf.0)
          (let ()
            (match-define (cons the-cost best-r)
                          (if (empty? rs)
                              (cons 1 empty)
                              (argmin car
                                      (mark-parameterize ([cycle-detect p])
                                                         (for/list ([r (in-list rs)])
                                                           (cons (apply + (map compute-cost! r)) r))))))
            (if (= +inf.0 the-cost)
                +inf.0
                (begin
                  (set! computed? #t)
                  (set-entry-recipes! e best-r)
                  (set-entry-cost! e (+ lvl the-cost))
                  (entry-cost e)))))))

(let loop ()
  (set! computed? #f)
  (for ([p (in-hash-keys db)])
    (compute-cost! p))
  (when computed?
    (printf "Looping\n")
    (loop)))

(define es (hash-map db cons))

(for ([p*e (in-list (sort es < #:key (compose entry-cost cdr)))])
  (match-define (cons p (entry cost lvl rs ns)) p*e)
  (printf "Lvl ~a. ~a\n\t~v\n" lvl p rs))


