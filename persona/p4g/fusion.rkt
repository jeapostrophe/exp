#lang racket/base
(require racket/list
         racket/match
         (prefix-in data: "data.rkt"))
(module+ test
  (require rackunit))

(define (fusion-result arcana level #:same? [same? #f])
  (define ps
    (filter
     (λ (p)
       (not (memf (λ (e) (string=? (first e) (data:persona-name p)))
                  data:special)))
     (hash-ref data:arcana->personas arcana
               (λ ()
                 (error 'fusion-result
                        "Arcana ~a unknown"
                        arcana)))))

  (let loop ([ps ps])
    (cond
      [(empty? (rest ps))
       (data:persona-name (first ps))]
      [(< level (data:persona-lvl (second ps)))
       (if same?
         (data:persona-name (first ps))
         (data:persona-name (second ps)))]
      [else
       (loop (rest ps))])))

(module+ test
  (check-equal? (fusion-result 'Star 49)
                "Ganesha")
  (check-equal? (fusion-result 'Tower 80)
                "Masakado")
  (check-equal? (fusion-result 'Temperance 57)
                "Byakko")
  (check-equal? (fusion-result 'Fool 32)
                "Decarabia")
  (check-equal? (fusion-result 'Fool 32 #:same? #t)
                "Ose"))

(define (arcana->i a)
  (for/or ([some-a (in-list data:arcana)]
           [i (in-naturals)])
    (and (eq? a some-a)
         i)))

(define (normal-chart-lookup left-a right-a)
  (define left-i (arcana->i left-a))
  (define right-i (arcana->i right-a))
  (define low-i (min left-i right-i))
  (define max-i (max left-i right-i))
  (define max-c (list-ref data:fusion-chart max-i))
  (list-ref max-c low-i))

(module+ test
  (check-equal? (normal-chart-lookup 'Justice 'Strength)
                'Temperance))

(define (double-fusion left right)
  (match-define (data:persona left-a left-l _)
                (hash-ref data:name->persona left
                          (λ () (error 'double-fusion
                                       "Persona ~a unknown"
                                       left))))
  (match-define (data:persona right-a right-l _)
                (hash-ref data:name->persona right
                          (λ () (error 'double-fusion
                                       "Persona ~a unknown"
                                       right))))
  (define result-a (normal-chart-lookup left-a right-a))
  (and result-a
       (fusion-result result-a
                      (+ (/ (+ left-l right-l)
                            2)
                         1)
                      #:same? (eq? left-a right-a))))

(module+ test
  (check-equal? (double-fusion "Throne" "Siegfried")
                "Byakko")
  (check-equal? (double-fusion "Ose" "Legion")
                "Legion"))

(define (triangle-chart-lookup left-a right-a)
  (define left-i (arcana->i left-a))
  (define right-i (arcana->i right-a))
  (define low-i (min left-i right-i))
  (define max-i (max left-i right-i))
  (define low-r (list-ref data:fusion-chart low-i))
  (list-ref low-r max-i))

(define (triple-fusion p1 p2 p3)
  (define ps
    (map (λ (n) (hash-ref data:name->persona n
                          (λ () (error 'triple-fusion
                                       "Persona ~a unknown"
                                       n))))
         (list p1 p2 p3)))
  (match-define
   (list (data:persona lo-a lo-l _)
         (data:persona mi-a mi-l _)
         (data:persona hi-a hi-l _))
   (sort ps
         (λ (p1 p2)
           (match-define (data:persona a1 l1 _) p1)
           (match-define (data:persona a2 l2 _) p2)
           (if (= l1 l2)
             (< (arcana->i a1) (arcana->i a2))
             (< l1 l2)))))
  (define int-a (normal-chart-lookup lo-a mi-a))
  (and int-a
       (let ()
         (define tri-a (triangle-chart-lookup int-a hi-a))
         (and tri-a
              (fusion-result 
               (+ (/ (+ lo-l mi-l hi-l) 3) 5))))))

(module+ test
  (check-equal? (triple-fusion "Senri" "Throne" "Loki")
                "Lachesis")
  (check-equal? (triple-fusion "Throne" "Senri" "Loki")
                "Lachesis")
  (check-equal? (triple-fusion "Throne" "Loki" "Senri")
                "Lachesis"))

(provide (all-defined-out))
