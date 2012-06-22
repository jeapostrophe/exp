#lang racket/base
(require racket/list)

(define map
  '((2 1 1 2)
    (1 2 2 1)
    (1 1 1 2)
    (2 2 1 1)))

(define node->node
  (for/fold ([node->node (hash)])
      ([row (in-list map)]
       [i (in-naturals)])
    (for/fold ([node->node node->node])
        ([val (in-list row)]
         [j (in-naturals)])
      (hash-set node->node (cons i j)
                (list
                 (cons (- i val) j)
                 (cons (+ i val) j)
                 (cons i (- j val))
                 (cons i (+ j val)))))))

(define (search-from node->node path start)
  (cond
    [(zero? (hash-count node->node))
     path]
    [else
     (for/or ([next (in-list (hash-ref node->node start empty))])
       (search-from (hash-remove node->node start)
                    (append path (list next))
                    next))]))

(define k (cons 2 0))
(define ans
  (search-from node->node (list k) k))

(module+ main
  (for ([n (in-list (reverse (rest (reverse ans))))])
    (printf "~a ->\n" n)))
