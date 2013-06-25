#lang racket/base
(require racket/list
         racket/match)
(module+ test
  (require rackunit))

(define (building->drawing x y b)
  (match-define (list l h r) b)
  (eprintf "~a ~a ~a\n" x y b)

  (cond
    [(= y h)
     (values empty r h)]
    [(= x l)
     (values (list (list l h)) r h)]
    [else
     (values (list (list x 0) (list l h)) r h)]))

(define (height-map->drawing hm)
  (define (inner x y hm)
    (match hm
      [#f
       (values empty x y)]
      [(list tl b tr)
       (define-values (tld tl-x tl-y) (inner x y tl))
       (define-values (bd b-x b-y) (building->drawing tl-x tl-y b))
       (define-values (trd tr-x tr-y) (inner b-x b-y tr))
       (values (append tld bd trd) tr-x tr-y)]))
  (define-values (hmd hm-x hm-y) (inner 0 0 hm))
  (rest (append hmd (list (list hm-x 0)))))

(define empty-hm #f)

(define (split n c)
  (match-define (list nl nh nr) n)
  (match-define (list cl ch cr) c)
  (cond
    ;; Case 1
    [(and (<= nl cr) (< nh ch) (< cr nr))
     (list #f c (list cr nh nr))]
    ;; Case 2
    [(and (< cl nr) (< ch nh) (< nr cr))
     (list n (list nr ch cr) #f)]
    ;; Case 3
    [(and (< cl nl) (< ch nh) (< cr nr))
     (list (list cl ch nl)
           (list nl nh cr)
           (list cr nh nr))]
    ;; Case 4
    [(and (<= cl nl) (< nh ch) (<= nr cr))
     (list #f c #f)]
    ;; Case 5
    [(and (= cl nl) (< ch nh) (< cr nr))
     (list #f
           (list nl nh cr)
           (list cr nh nr))]
    [else
     (error 'split "~a ~a" n c)]))

(module+ test
  ;; Case 1
  (check-equal? (split '(2 6 7) '(1 11 5))
                (list #f
                      '(1 11 5)
                      '(5 6 7)))
  ;; Case 2
  (check-equal? (split '(1 11 5) '(2 6 7))
                (list '(1 11 5)
                      '(5 6 7)
                      #f))
  ;; Case 3
  (check-equal? (split '(3 13 9) '(1 11 5))
                (list '(1 11 3)
                      '(3 13 5)
                      '(5 13 9)))
  ;; Case 1 (generalize to <=)
  (check-equal? (split '(22 3 23) '(19 18 22))
                (list #f
                      '(19 18 22)
                      '(22 3 23)))
  ;; Case 4
  (check-equal? (split '(24 4 28) '(23 13 29))
                (list #f
                      '(23 13 29)
                      #f))
  ;; Case 5
  (check-equal? (split '(5 13 9) '(5 6 7))
                (list #f
                      '(5 13 7)
                      '(7 13 9)))
  ;; Case 4 (generalize to <=)
  (check-equal? (split '(25 4 28) '(25 13 29))
                (list #f
                      '(25 13 29)
                      #f)))

(define (insert* b hm)
  (if b
    (insert b hm)
    hm))

(define (insert b hm)
  (match-define (list l h r) b)
  (match hm
    [#f
     (list #f b #f)]
    [(list to-the-left (and tb (list tl _ tr)) to-the-right)
     (cond
       [(< r tl)
        (list (insert b to-the-left) tb to-the-right)]
       [(< tr l)
        (list to-the-left tb (insert b to-the-right))]
       [else
        (match-define (list nl nm nr) (split b tb))
        (list (insert* nl to-the-left)
              nm
              (insert* nr to-the-right))])]))

(define (skyline bs)
  (foldl insert empty-hm bs))

(define (skyline* l)
  (height-map->drawing (skyline l)))

(module+ test
  (check-equal?
   (skyline*
    '((1 11 5) (2 6 7) (3 13 9) (12 7 16) (14 3 25) (19 18 22) (23 13 29) (24 4 28)))
   '((1 11) (3 13) (9 0) (12 7) (16 3) (19 18) (22 3) (23 13) (29 0))))
