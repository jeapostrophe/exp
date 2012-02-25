#lang racket

(define vals (list 5 1 4 4 1 3 3 5 2 1 5))
(define how-many (length vals))
(define node->val (make-hasheq))
(define node->node
  (for/fold
      ([node->node (hasheq)])
      ([val (in-list vals)]
       [pos (in-naturals)])
    (hash-set! node->val pos val)
    (hash-set node->node pos
              (list (modulo (- pos val) how-many)
                    (modulo (+ pos val) how-many)))))

(when #f
  (printf "digraph {\n")
  (for* ([(node nexts) (in-hash node->node)]
         [next (in-list nexts)])
    (printf "~a -> ~a\n" node next))
  (printf "}\n"))

(define (search-from node->node path start)
  (cond
    [(zero? (hash-count node->node))
     path]
    [else
     (for/or ([next (in-list (hash-ref node->node start empty))])
       (search-from (hash-remove node->node start)
                    (append path (list next))
                    next))]))

(define ans
  (for/or ([k (in-hash-keys node->node)])
    (search-from node->node (list k) k)))

(for ([n (in-list (reverse (rest (reverse ans))))])
  (printf "~a/~a ->\n" n (hash-ref node->val n)))
