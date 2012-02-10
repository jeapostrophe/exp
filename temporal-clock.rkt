#lang racket

(define vals (list 1 2 4 4 2 3 1 3 1 5))
(define how-many (length vals))
(define node->node
  (for/fold
   ([node->node (hasheq)])
   ([val (in-list vals)]
    [pos (in-naturals)])
   (hash-set node->node pos
             (list (modulo (- pos val) how-many)
                   (modulo (+ pos val) how-many)))))

(printf "digraph {\n")
(for* ([(node nexts) (in-hash node->node)]
       [next (in-list nexts)])
      (printf "~a -> ~a\n" node next))
(printf "}\n")

(define (search-from node->node path start)
  (cond
   [(zero? (hash-count node->node))
    path]
   [else
    (for/or ([next (in-list (hash-ref node->node start empty))])
            (search-from (hash-remove node->node start)
                         (append path (list next))
                         next))]))

(time (search-from node->node (list 6) 6))

(time (for/or ([k (in-hash-keys node->node)])
              (search-from node->node (list k) k)))
