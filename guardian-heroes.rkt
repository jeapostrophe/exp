#lang racket/base
(require graph
         racket/list
         racket/string
         racket/match
         racket/set
         racket/file
         racket/format
         racket/system)

(define STAGES
  '([start 1]
    [1 2]
    [2 4 5 3]
    [3 6 8]
    [4 12 7]
    [5 11 10 9]
    [6 11 10 9]
    [7 11 10 9]
    [8 13 14 15 16 17]
    [9 13 14 15 16 17]
    [10 13 14 15 16 17]
    [11 13 14 15 16 17]
    [12 13 14 15 16 17]
    [13 18 19 20]
    [14 18 19 20]
    [15 19 20 21 22]
    [16 21 22 23]
    [17 21 22 23]
    [18 24 25]
    [19 24 25 26]
    [20 24 25 26]
    [21 26 27 28]
    [22 26 27 28]
    [23 27 28]
    [24 end]
    [25 end]
    [26 29]
    [27 30]
    [28 end]
    [29 end]
    [30 end]
    [end]))

(define (chase prev-ht n)
  (define next (hash-ref prev-ht n #f))
  (if next
    (cons n (chase prev-ht next))
    (list n)))

(define (go! seen?)
  (define g (weighted-graph/directed '()))
  (define all-seen?
    (for/fold ([all-seen? #t]) ([edge (in-list STAGES)])
      (match-define (cons u ns) edge)
      (for ([v (in-list ns)])
        (add-directed-edge!
         g u v
         (if (set-member? seen? v) 0 -1)))
      (and all-seen? (set-member? seen? u))))
  (cond
    [all-seen?
     empty]
    [else
     (define-values (dist-ht prev-ht)
       (dag-shortest-paths g 'start))
     (define pth (chase prev-ht 'end))
     (cons (rest (reverse (rest pth)))
           (go! (set-union seen? (list->seteq pth))))]))

(define (render-graphviz/dot dot png)
  (system (~a "dot "dot" -Tpng -o "png)))
(define (render-graphviz dot-content png)
  (define tmp (make-temporary-file))
  (displayln dot-content)
  (display-to-file dot-content tmp #:exists 'replace)
  (render-graphviz/dot tmp png)
  (delete-file tmp))

(define (render-graph g png)
  (render-graphviz (graphviz g) png))

(define (which u v)
  (for/or ([n (in-list STAGES)]
           #:when (eq? u (first n)))
    (if (= 1 (length (rest n)))
      ""
      (for/or ([n (in-list (rest n))]
               [i (in-naturals 1)]
               #:when (eq? v n))
        (~a " "i)))))

(define (same-rank ns)
  (list "{ rank=same; "
        (for/list ([n (in-list ns)])
          (~a " node" n ";"))
        " }\n"))

(module+ main
  (require racket/pretty)
  (define all (unweighted-graph/adj STAGES))
  (remove-vertex! all 'end)
  (remove-vertex! all 'start)
  (render-graph all "STAGES.png")

  (define paths (go! (seteq)))
  (render-graphviz
   (string-join
    (flatten
     (list
      "digraph {\n"
      #;"\tordering=out;"
      (for/list ([n (in-set (apply set-union (map list->seteq paths)))])
        (~a "\tnode"n" [label=\""n"\"];\n"))
      (for/list ([pth (in-list paths)]
                 [i (in-naturals 1)])
        (list "subgraph {\n"
              (for/list ([u (in-list pth)]
                         [v (in-list (rest pth))])
                (define w (which u v))
                (~a "\tnode"u" -> node"v" [colorscheme=\"dark28\", color="i", label=\""w"\"];\n"))
              "}\n"))
      ;; XXX Hack
      (same-rank '(29 30))
      (same-rank '(24 25 26 27 28))
      (same-rank '(18 19 20 21 22 23))
      (same-rank '(13 14 15 16 17))
      (same-rank '( 8  9 10 11 12))
      (same-rank '( 5  6  7))
      (same-rank '( 3  4))      
      "}\n")))
   "PATHS.png"))
