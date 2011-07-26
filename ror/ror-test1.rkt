#lang racket/base
(require web-server/servlet
         "ror.rkt")

(define (post-render id)
  (define obj (hash-ref *posts* id))
  `(div (h2 ,(posts-title obj))
        ,(posts-body obj)))

(define (index req)
  (response/xexpr
   `(html
     (head (title "My Racket on Rockets blog"))
     (body
      (h1 "My Racket on Rockets blog")
      ,@(for/list ([last-post-n (in-range 5)])
          (define post-id (- (hash-count *posts*) (add1 last-post-n)))
          (if (negative? post-id)
              '(div)
              (post-render post-id)))
      (p (a ([href ,(to-url posts-new)]) "New Post") " "
         (a ([href ,(to-url posts-index)]) "All Posts"))))))

(blast-off!
 [posts (title body)])