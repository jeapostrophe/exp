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

(define (dat->info p want? ignore)
  (define xe
    (parameterize ([collapse-whitespace #t]
                   [xexpr-drop-empty-attributes #t])
      (string->xexpr (file->string p))))

  (define roms empty)
  (define n->r (make-hash))
  (let ()
    (define n->cs (make-hash))
    (for ([x (in-list xe)])
      (match x
        [(or 'datafile " " `(header . ,_)) (void)]
        [`(game ,attrs . ,body)
         (define name (dict-ref* attrs 'name))
         (unless (set-member? ignore name)
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
             (hash-update! n->cs parent (λ (old) (cons r old)) empty)))]
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

  (values roms
          n->r))

(define (go! fba-p mame-p d)
  (match-define (list fw mw) (file->value d))
  (define fba-want? (list->set (map symbol->string fw)))
  (define mame-want? (list->set (map symbol->string mw)))

  (define-values (fba-roms fba-n->r)
    (dat->info fba-p fba-want? (set)))
  (define-values (mame-roms mame-n->r)
    (dat->info mame-p mame-want? (list->set (hash-keys fba-n->r))))

  (define (display-tree i)
    (cond
      [(zero? i)
       (printf "│-- ")]
      [else
       (printf "│   ")
       (display-tree (sub1 i))]))
  (define bold-on "\033[1m")
  (define bold-off "\033[0m")
  (define (print-rom w! i r)
    (match-define (rom n d m y c? w? p cs) r)
    (when w? (printf bold-on))
    (display-tree i)
    (printf "~a. ~a\t< ~a >\t~a" y n m d)
    (when w? (printf bold-off))
    (printf "\n")
    (when w? (w! n))
    (print-roms w! (add1 i) cs))
  (define (print-roms w! i rs)
    (for ([r (in-list (sort rs string<=? #:key rom-year))])
      (print-rom w! i r)))

  ;; xxx copy want
  (define (print&collect label roms)
    (define w empty)
    (define (w! n) (set! w (cons n w)))
    
    (printf "~a:\n" label)
    (print-roms w! 0 roms)
    (printf "\n")

    (eprintf "\n~a\n\n" w))

  (print&collect "FBA" fba-roms)
  (print&collect "MAME" mame-roms))

(module+ main
  (require racket/cmdline)
  (command-line #:args (fba-p mame-p d) (go! fba-p mame-p d)))
