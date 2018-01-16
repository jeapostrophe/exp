#lang at-exp racket/base
(require racket/match
         racket/sequence
         racket/list
         racket/set
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
            (list "\t{" (add-between os ",") "},\n"))
         ]@";"


        % decision variables
        % the assignment of persons to a slot (appointment number 1..n)
        array[1..n] of var 1..n: x@";"

        solve satisfy@";"

        constraint
        1=1
        % ensure that the appointed person for the time slot is free
        %forall(i in 1..n) ( x[i] in s[i] )
        %/\ % ensure that each person get a distinct time slow
        %alldifferent(x)
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

(define (go/mzn! p)
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
  (define all-opts (sequence->list (in-range (hash-count i->slot))))
  (define i->candidate-info
    (for/hasheq ([c (in-list candidates)]
                 [i (in-naturals)])
      (match-define (cons name openings) c)
      (define file-opts
        (for/list ([o (in-list openings)]
                   [j (in-naturals)]
                   #:when (string=? o "x"))
          j))
      (define opts
        (if (empty? file-opts)
          all-opts
          file-opts))
      (values i (cons name opts))))
  (define mt (generate-mzn i->candidate-info))
  (print-tree mt)
  (define-values (sp stdout stdin stderr)
    (subprocess #;#f (current-output-port)
                #f (current-error-port)
                (find-executable-path "mzn-fzn")
                "-f" "fzn-gecode"
                "-I" "/usr/local/Cellar/gecode/5.1.0/share/gecode/mznlib"
                "--no-output-ozn"
                "-n" "1"
                "-"))
  (parameterize ([current-output-port stdin])
    (print-tree mt))
  (close-output-port stdin)
  (subprocess-wait sp))

(define (go! p)
  (local-require non-det)

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
  (define all-opts (sequence->list (in-range (hash-count i->slot))))
  (define candidate-infos
    (for/list ([c (in-list candidates)]
               [i (in-naturals)])
      (match-define (cons name openings) c)
      (define file-opts
        (for/list ([o (in-list openings)]
                   [j (in-naturals)]
                   #:when (string=? o "x"))
          j))
      (define opts
        (if (empty? file-opts)
          all-opts
          file-opts))
      (cons name (list->seteq opts))))
  (define sorted-candidate-infos
    (sort candidate-infos <= #:key (λ (ci) (set-count (cdr ci)))))  

  (struct sol (left-over slot->candidate) #:transparent)
  (define (search available slot->candidate cis)
    (match cis
      ['() (ans (sol available slot->candidate))]
      [(cons (cons name opts) more)
       (ndo [the-opt (ans* (in-set opts))]
            (if (set-member? available the-opt)
              (search (set-remove available the-opt)
                      (hash-set slot->candidate the-opt name)
                      more)
              fail))]))

  (define the-sol
    (nrun #:k 1 #:mode 'dfs
          (search (list->seteq all-opts) (hasheq)
                  sorted-candidate-infos)))
  (pretty-print the-sol))

(module+ main
  (go!
   (build-path (find-system-path 'home-dir)
               "Downloads"
               "Candidate Rating Matrix - Phone Planning.csv")))
