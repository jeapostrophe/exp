#lang at-exp racket/base
(require racket/match
         racket/list
         csv-reading
         racket/pretty)

(define (generate-mzn i->candidate-info)
  (define how-many (hash-count i->candidate-info))
  @list{
        include "globals.mzn"@";"
        int: n = @|how-many|@";"

        % free persons per time slot
        array[1..n] of set of int: s =
        [
         @(for/list ([i (in-range how-many)])
            (define os (cdr (hash-ref i->candidate-info i)))
            (list "{" (add-between os ",") "},"))
        ]@";"


        % decision variables
        % the assignment of persons to a slot (appointment number 1..n)
        array[1..n] of var 1..n: x@";"

        solve satisfy@";"

        constraint
        % ensure that the appointed person for the time slot is free
        forall(i in 1..n) ( x[i] in s[i] )
        /\ % ensure that each person get a distinct time slow
        alldifferent(x)
        @";"

        output [ show(x) ]@";"})

(define (print-tree x)
  (match x
    [(cons a d)
     (print-tree a)
     (print-tree d)]
    [(or (? string?)
         (? number?))
     (display x)]
    [_ (void)]))

(define (go! p)
  (define in
    (call-with-input-file p
      (λ (ip)
        (csv->list
         (make-csv-reader ip)))))
  (match-define (cons (cons _ slots) candidates) in)
  (define i->slot
    (for/hasheq ([s (in-list slots)]
                 [i (in-naturals)])
      (values i s)))
  (define i->candidate-info
    (for/hasheq ([c (in-list candidates)]
                 [i (in-naturals)])
      (match-define (cons name openings) c)
      (values i (cons name
                      (for/list ([o (in-list openings)]
                                 [j (in-naturals)]
                                 #:when (string=? o "x"))
                        j)))))
  (define mt (generate-mzn i->candidate-info))
  (define sp
    (subprocess #f #f #f))
  (print-tree mt))

(module+ main
  (go!
   (build-path (find-system-path 'home-dir)
               "Downloads"
               "Candidate Rating Matrix - Phone Planning.csv")))
