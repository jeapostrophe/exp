#lang racket/base
(require graph
         racket/file
         racket/format
         racket/system)

(define STAGES
  (unweighted-graph/adj
   '([1 2]
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
     [end])))

(define (render-graphviz dot png)
  (system (~a "dot "dot" -Tpng -o "png)))
(define (render-graph g png)
  (define tmp (make-temporary-file))
  (display-to-file (graphviz g) tmp #:exists 'replace)
  (render-graphviz tmp png)
  (delete-file tmp))

(module+ main
  (render-graph STAGES "STAGES.png")
  (render-graph (unweighted-graph/directed (mst-prim STAGES 1)) "MST.png"))
