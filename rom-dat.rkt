#lang racket/base
(require racket/match
         racket/list
         racket/file
         racket/dict
         racket/set
         racket/system
         xml)

(struct rom (name desc manu year clone? want? parent children) #:mutable)

(define (dict-ref* d k)
  (match (dict-ref d k #f)
    [(list v) v]
    [#f #f]))

(define (go! p d)
  (define xe
    (parameterize ([collapse-whitespace #t]
                   [xexpr-drop-empty-attributes #t])
      (string->xexpr (file->string p))))
  (define want? (list->set (map symbol->string (file->value d))))

  (define roms empty)
  (let ()
    (define n->r (make-hash))
    (define n->cs (make-hash))
    (for ([x (in-list xe)])
      (match x
        [(or 'datafile " " `(header . ,_)) (void)]
        [`(game ,attrs . ,body)
         (define name (dict-ref* attrs 'name))
         (define desc "Unknown")
         (define year "????")
         (define manu "Unknown")
         (for ([x (in-list body)])
           (match x
             [`(description . ,d) (set! desc d)]
             [`(year ,y) (set! year y)]
             [`(manufacturer ,m) (set! manu m)]
             [x (void)]))
         (define clone? (and (dict-ref* attrs 'cloneof) #t))
         (define parent (dict-ref* attrs 'romof))
         (define w? (set-member? want? name))

         (define r (rom name desc manu year clone? w? parent empty))
         (hash-set! n->r name r)
         (when parent
           (hash-update! n->cs parent (λ (old) (cons r old)) empty))]
        [x
         (printf "~e\n" x)]))
    
    (for ([(n r) (in-hash n->r)])
      (define cs (hash-ref n->cs n empty))
      (set-rom-children! r cs)
      (unless (or (rom-parent r) (empty? cs))
        (set! roms (cons r roms)))))

  (let loop ([r roms])
    (cond
      [(rom? r)
       (define c (loop (rom-children r)))
       (define w? (or (rom-want? r) c))
       (set-rom-want?! r w?)
       w?]
      [(cons? r)
       (define x (loop (car r)))
       (define y (loop (cdr r)))
       (or x y)]
      [else
       #f]))

  (define (display-tree i)
    (cond
      [(zero? i)
       (display "│-- ")]
      [else
       (display "│   ")
       (display-tree (sub1 i))]))
  (define bold-on "\033[1m")
  (define bold-off "\033[0m")
  (define (print-rom i r)
    (match-define (rom n d m y c? w? p cs) r)
    (when w? (display bold-on))
    (display-tree i)
    (printf "~a. ~a\t< ~a >\t~a" y n m d)
    (when w? (display bold-off))
    (newline)
    (print-roms (add1 i) cs))
  (define (print-roms i rs)
    (for ([r (in-list (sort rs string<=? #:key rom-year))])
      (print-rom i r)))

  ;; xxx copy want
  (print-roms 0 roms))

(module+ main
  (require racket/cmdline)
  (command-line #:args (p d) (go! p d)))
