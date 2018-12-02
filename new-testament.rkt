#lang racket/base
(require racket/list
         racket/match
         racket/pretty)

(define nt
  '((Mark 16  45  28  35  41  43  56  37  38  50  52  33  44  37  72  47  20  0   0   0   0   0   0   0   0   0   0   0   0   678)
    (Matt 28  25  23  17  25  48  34  29  34  38  42  30  50  58  36  39  28  27  35  30  34  46  46  39  51  46  75  66  20  1071)

    (Luke-Acts 24  80  52  38  44  39  49  50  56  62  42  54  59  35  35  32  31  37  43  48  47  38  71  56  53  0   0   0   0   1151)
    (Luke-Acts 28  26  47  26  37  42  15  60  40  43  48  30  25  52  28  41  40  34  28  40  38  40  30  35  27  27  32  44  31  1006)
    (John 21  51  25  36  54  47  71  53  59  41  42  57  50  38  31  27  33  26  40  42  31  25  0   0   0   0   0   0   0   879)))

(module+ main
  (define rnt (map reverse nt))
  (define total-verses (foldr + 0 (map first rnt)))
  (define verses-per-week
    (* 0.80 (/ total-verses 52.0)))
  verses-per-week
  (define counts (map (λ (x) (reverse (rest x))) rnt))
  (define chapter-count
    (append-map (λ (x)
                  (match-define (list* book _ counts) x)
                  (for/list ([c (in-list counts)] [ch (in-naturals 1)] #:unless (zero? c))
                    (cons (cons book ch) c)))
                counts))

  (let loop ([i 1] [wk empty] [vr verses-per-week] [cs chapter-count])
    (cond
      [(or (empty? cs)
           (not (positive? vr))
           (and (not (empty? wk))
                (not (eq? (car (car (first cs)))
                     (car (car (first wk)))))))
       (printf "Week ~a. (~a)\n" i vr)
       (for ([c (in-list (reverse wk))])
         (printf "\t~v\n" c))       
       (unless (empty? cs)
         (loop (add1 i) empty (+ #;vr verses-per-week) cs))]      
      [else
       (match-define (cons (and this (cons which vs)) more) cs)
       (loop i (cons this wk) (- vr vs) more)])))
