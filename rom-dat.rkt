#lang racket/base
(require racket/match
         racket/list
         racket/file
         racket/dict
         racket/set
         racket/system
         graph
         xml)

(define (go! p)
  (define xe
    (parameterize ([collapse-whitespace #t]
                   [xexpr-drop-empty-attributes #t])
      (string->xexpr (file->string p))))
  
  (define g (directed-graph empty))
  (define n->y (make-hash))
  (define n->d (make-hash))
  (define clones (mutable-set))
  
  (for ([x (in-list xe)])
    (match x
      [(or 'datafile " " `(header . ,_)) (void)]
      [`(game ,attrs . ,body)
       (define n (first (dict-ref attrs 'name)))
       (add-vertex! g n)
       (when (dict-ref attrs 'cloneof #f)
         (set-add! clones n))
       ;; xxx sampleof
       (define r (dict-ref attrs 'romof #f))
       (when r
         (add-edge! g n (first r)))
       (for ([x (in-list body)])
         (match x
           [`(description ,d) (hash-set! n->d n d)]
           [`(year ,y) (hash-set! n->y n y)]
           [x (void)]))]
      [x
       (printf "~e\n" x)]))

  (define dot-p (path-add-suffix p #".dot"))
  (define pdf-p (path-add-suffix p #".pdf"))
  (display-to-file (graphviz g) dot-p)
  (system* (find-executable-path "dot")
           "-Tpdf" dot-p "-o" pdf-p)

  (for ([n (in-vertices g)])
    (printf "~a (~a)\n" (hash-ref n->d n) n))
  
  )

(module+ main
  (require racket/cmdline)
  (command-line #:args (p) (go! p)))
