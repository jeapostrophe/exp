#lang racket/base
(require (for-syntax racket/base
                     racket/list
                     syntax/parse)
         racket/function
         racket/match
         racket/list)

(define-syntax-rule (define-check id S)
  (define (id s)
    (if (member s S)
      s
      (error 'id "~v not in ~v" s S))))
(define-check check-LR '(L R))

(struct *tm (initial states inputs blank final? delta) #:transparent)
(define-syntax (tm stx)
  (syntax-parse stx
    [(_ #:Q (state ...)
        #:G (sym ...)
        #:b blank
        #:S (input ...)
        #:q0 initial-state
        #:F (final-state ...)
        #:delta
        [(delta-state delta-symbol)
         (next-state write-symbol head-movement)]
        ...)
     (syntax/loc stx
       (let ()
         (define-check check-G '(sym ...))
         (define-check check-Q '(state ...))
         (*tm (check-Q 'initial-state)
              '(state ...)
              (list (check-G 'input) ...)
              (if (member 'blank '(input ...))
                (error 'tm "Blank cannot be in input alphabet")
                (check-G 'blank))
              (make-hasheq
               (list (cons (check-Q 'final-state) #t)
                     ...))
              (make-hash
               (list (cons (cons (check-Q 'delta-state)
                                 (check-G 'delta-symbol))
                           (list (check-Q 'next-state)
                                 (check-G 'write-symbol)
                                 (check-LR 'head-movement)))
                     ...)))))]))

(define (truncate-trailing x l)
  (let loop ([y empty] [m empty] [l l])
    (cond
      [(empty? l)
       (reverse y)]
      [(eq? x (first l))
       (loop y (list* x m) (rest l))]
      [else
       (define ny (list* (first l) m))
       (loop ny ny (rest l))])))

(struct tape (blank before after))
(define (tape-first t)
  (match-define (tape b before after) t)
  (match after
    [(cons h _) h]
    [(list) b]))
(define (tape-rest t)
  (match-define (tape b before after) t)
  (match after
    [(cons h r) r]
    [(list) empty]))
(define (tape-tser t)
  (reverse (tape-before t)))
(define (tape->list t)
  (append (reverse (truncate-trailing (tape-blank t) (tape-before t)))
          (truncate-trailing (tape-blank t) (tape-after t))))

(define (tape-move-left t)
  (match-define (tape b before after) t)
  (match before
    [(cons b-hd b-tl)
     (tape b b-tl (cons b-hd after))]
    [(list)
     (tape b empty (cons b after))]))
(define (tape-move-right t)
  (match-define (tape b before after) t)
  (match after
    [(cons a-hd a-tl)
     (tape b (cons a-hd before) a-tl)]
    [(list)
     (tape b (cons b before) empty)]))

(define (tape-write t w)
  (match-define (tape b before after) t)
  (match after
    [(cons h t)
     (tape b before (cons w t))]
    [(list)
     (tape b before (list w))]))

(struct *state (state tape))
(define (step tm s)
  (match-define (*tm _ _ _ _ final? delta) tm)
  (match-define (*state st t) s)
  (cond
    [(hash-ref final? st #f)
     s]
    [else
     (define h (tape-first t))
     (match-define
      (list n-st w dir)
      (hash-ref delta (cons st h)
                (λ ()
                  (error 'step "No transition defined for ~v in ~v state"
                         h st))))
     (define n-t (tape-write t w))
     (define nn-t
       (if (eq? 'L dir)
         (tape-move-left n-t)
         (tape-move-right n-t)))
     (*state n-st nn-t)]))

(define (step-n tm s n
                #:inform [inform-f void])
  (let loop ([i 0] [n n] [s s])
    (inform-f i s)
    (cond
      [(zero? n)
       s]
      [else
       (define ns (step tm s))
       (if (eq? s ns)
         s
         (loop (add1 i) (sub1 n) ns))])))

(define (run tm input steps
             #:inform [inform-f void])
  (define (valid-input? s)
    (member s (*tm-inputs tm)))
  (for ([s (in-list input)])
    (unless (valid-input? s)
      (error 'run "Invalid input: ~e" s)))

  (define initial-s
    (*state
     (*tm-initial tm)
     (tape (*tm-blank tm)
           empty
           input)))
  (define final-s
    (step-n tm initial-s steps
            #:inform inform-f))
  (tape->list
   (*state-tape final-s)))

(define (run* tm input
              #:inform [inform-f void])
  (run tm input +inf.0 #:inform inform-f))

(require racket/format
         racket/string)
(define (make-display-state tm)
  (define max-st-len
    (apply max
           (map (compose string-length symbol->string)
                (*tm-states tm))))
  (λ (i s)
    (match-define (*state st t) s)
    (displayln
     (~a (~a #:min-width max-st-len st) ": "
         (string-append* (map ~a (tape-tser t)))
         "[" (tape-first t) "]"
         (string-append* (map ~a (tape-rest t)))
         " {" (~a i) "}"))))

(module+ test
  ;; xxx why do i need this?
  (require (except-in rackunit define-check))

  (define busy-beaver
    (tm #:Q (A B C HALT)
        #:G (0 1)
        #:b 0
        #:S (1)
        #:q0 A
        #:F (HALT)
        #:delta
        [(A 0) (   B 1 R)]
        [(A 1) (   C 1 L)]
        [(B 0) (   A 1 L)]
        [(B 1) (   B 1 R)]
        [(C 0) (   B 1 L)]
        [(C 1) (HALT 1 R)]))

  (check-equal?
   (run* busy-beaver
         '()
         #:inform (make-display-state busy-beaver))
   '(1 1 1 1 1 1))

  (define unary-addition
    (tm #:Q (consume-first-number
             consume-second-number
             override-last-*
             seek-beginning
             HALT)
        #:G (* _ /)
        #:b _
        #:S (* /)
        #:q0 consume-first-number
        #:F (HALT)
        #:delta
        [(consume-first-number *)
         (consume-first-number * R)]
        [(consume-first-number /)
         (consume-second-number * R)]
        [(consume-second-number *)
         (consume-second-number * R)]
        [(consume-second-number _)
         (override-last-* _ L)]
        [(override-last-* *)
         (seek-beginning _ L)]
        [(seek-beginning *)
         (seek-beginning * L)]
        [(seek-beginning _)
         (HALT _ R)]))

  (check-equal?
   (run* unary-addition
         '(* * * * * / * * * * *)
         #:inform (make-display-state unary-addition))
   '(* * * * * * * * * *)))

(begin-for-syntax
  (define (syntax->slist s)
    (map syntax->datum (syntax->list s)))
  (define-syntax-rule (in-syntax s)
    (in-list (syntax->list s))))

(define-syntax (implicit-tm stx)
  (syntax-parse stx
    [(_ [idelta-state
         [idelta-symbol
          (inext-state iwrite-symbol ihead-movement)]
         ...]
        ...)
     (with-syntax
         ([(state ...)
           (remove-duplicates
            (cons 'HALT
                  (append (syntax->slist #'(idelta-state ...))
                          (syntax->slist #'(inext-state ... ...)))))]
          [(sym ...)
           (remove-duplicates
            (cons '_
                  (append (syntax->slist #'(idelta-symbol ... ...))
                          (syntax->slist #'(iwrite-symbol ... ...)))))]
          [(isym ...)
           (remove '_
                   (remove-duplicates
                    (syntax->slist #'(idelta-symbol ... ...))))]
          [(delta-state0 _ ...) #'(idelta-state ...)]
          [((delta-state
             delta-symbol
             (next-state write-symbol head-movement))
            ...)
           (for*/list
               ([i (in-syntax
                    #'([idelta-state
                        [idelta-symbol
                         (inext-state
                          iwrite-symbol
                          ihead-movement)]
                        ...]
                       ...))]
                [j (in-list
                    (rest (syntax->list i)))])
             (cons (first (syntax->list i))
                   (syntax->list j)))])
       (syntax/loc stx
         (tm #:Q (state ...)
             #:G (_ sym ...)
             #:b _
             #:S (isym ...)
             #:q0 delta-state0
             #:F (HALT)
             #:delta
             [(delta-state delta-symbol)
              (next-state write-symbol head-movement)]
             ...)))]))

(module+ test
  (define implicit-unary-addition
    (implicit-tm
     [consume-first-number
      [* (consume-first-number * R)]
      [+ (consume-second-number * R)]]
     [consume-second-number
      [* (consume-second-number * R)]
      [_ (override-last-* _ L)]]
     [override-last-*
      [* (seek-beginning _ L)]]
     [seek-beginning
      [* (seek-beginning * L)]
      [_ (HALT _ R)]]))

  (check-equal?
   (run* implicit-unary-addition
         '(* * * * * + * * * * *)
         #:inform (make-display-state implicit-unary-addition))
   '(* * * * * * * * * *))

  ;; 2 + 3 = 5
  (check-equal?
   (run* implicit-unary-addition
         '(* * + * * *)
         #:inform (make-display-state implicit-unary-addition))
   '(* * * * *))

  (define implicit-binary-add1
    (implicit-tm
     [find-end
      [0 (find-end 0 R)]
      [1 (find-end 1 R)]
      [_ (zero-until-0 _ L)]]
     [zero-until-0
      [1 (zero-until-0 0 L)]
      [0 (HALT 1 L)]]))

  (check-equal?
   (run* implicit-binary-add1
         '(0 0 1 0)
         #:inform (make-display-state implicit-binary-add1))
   '(0 0 1 1))

  (define implicit-binary-sub1
    (implicit-tm
     [ones-complement
      [0 (ones-complement 1 R)]
      [1 (ones-complement 0 R)]
      [_ (add1:zero-until-0 _ L)]]
     [add1:zero-until-0
      [1 (add1:zero-until-0 0 L)]
      [0 (add1:find-end 1 R)]]
     [add1:find-end
      [0 (add1:find-end 0 R)]
      [1 (add1:find-end 1 R)]
      [_ (ones-complementR _ L)]]
     [ones-complementR
      [0 (ones-complementR 1 L)]
      [1 (ones-complementR 0 L)]
      [_ (HALT _ R)]]))

  (check-equal?
   (run* implicit-binary-sub1
         '(0 0 1 1)
         #:inform (make-display-state implicit-binary-sub1))
   '(0 0 1 0))

  ;; (define (binary-add x y)
  ;;   (if (zero? x)
  ;;     y
  ;;     (binary-add (sub1 x) (add1 y))))

  (define implicit-binary-add
    (implicit-tm
     [check-if-zero
      [0 (check-if-zero 0 R)]
      [1 (seek-left&sub1 1 L)]
      [+ (seek-left&zero _ L)]]
     [seek-left&sub1
      [0 (seek-left&sub1 0 L)]
      [1 (seek-left&sub1 1 L)]
      [_ (sub1:ones-complement _ R)]]
     [sub1:ones-complement
      [0 (sub1:ones-complement 1 R)]
      [1 (sub1:ones-complement 0 R)]
      [+ (sub1:add1:zero-until-0 + L)]]
     [sub1:add1:zero-until-0
      [1 (sub1:add1:zero-until-0 0 L)]
      [0 (sub1:add1:find-end 1 R)]]
     [sub1:add1:find-end
      [0 (sub1:add1:find-end 0 R)]
      [1 (sub1:add1:find-end 1 R)]
      [+ (sub1:ones-complementR + L)]]
     [sub1:ones-complementR
      [0 (sub1:ones-complementR 1 L)]
      [1 (sub1:ones-complementR 0 L)]
      [_ (seek-right&add1 _ R)]]
     [seek-right&add1
      [0 (seek-right&add1 0 R)]
      [1 (seek-right&add1 1 R)]
      [+ (add1:find-end + R)]]
     [add1:find-end
      [0 (add1:find-end 0 R)]
      [1 (add1:find-end 1 R)]
      [_ (add1:zero-until-0 _ L)]]
     [add1:zero-until-0
      [1 (add1:zero-until-0 0 L)]
      [0 (seek-left&continue 1 L)]]
     [seek-left&continue
      [0 (seek-left&continue 0 L)]
      [1 (seek-left&continue 1 L)]
      [+ (seek-left&continue + L)]
      [_ (check-if-zero _ R)]]
     [seek-left&zero
      [0 (seek-left&zero _ L)]
      [_ (seek-start _ R)]]
     [seek-start
      [_ (seek-start _ R)]
      [0 (move-right-once 0 L)]
      [1 (move-right-once 1 L)]]
     [move-right-once
      [_ (HALT _ R)]]))

  ;; 2 + 3 = 5
  (check-equal?
   (run* implicit-binary-add
         '(0 0 1 0 + 0 0 1 1)
         #:inform (make-display-state implicit-binary-add))
   '(0 1 0 1))

  (check-equal?
   (run* implicit-binary-add
         '(0 0 1 1 0 + 0 1 0 1 1)
         #:inform (make-display-state implicit-binary-add))
   '(1 0 0 0 1))

  (check-equal?
   (run* implicit-binary-add
         '(0 1 1 + 0 1 1)
         #:inform (make-display-state implicit-binary-add))
   '(1 1 0)))

;; Rendering
(require 2htdp/universe
         2htdp/image)

(define (beside* l)
  (cond
    [(empty? l) empty-image]
    [(empty? (cdr l)) (car l)]
    [else
     (apply beside/align "bottom" l)]))
(define SIZE-FONT 30)
(define (render-cell s [focus? #f])
  (define t
    (text/font (~a s) SIZE-FONT
               "black"
               #f 'modern 'normal (if focus? 'bold 'normal) #f))
  (define d 2)
  (overlay/align
   "middle" "middle"
   t
   (rectangle (image-width t) (image-height t) "solid" "white")
   (rectangle (+ d (image-width t)) (+ d (image-height t)) "solid"
              (if focus? "red" "black"))))
(define CELL-HEIGHT
  (image-height (render-cell '0)))
(define CELL-WIDTH
  (image-width (render-cell '0)))
(define SIZE-T CELL-HEIGHT)
(define (draw-state s)
  (define W 500)
  (define H (* 5 CELL-HEIGHT))
  (match-define (*state st t) s)

  (define head-cell (render-cell (tape-first t) #t))
  (place-image/align
   (above/align "middle"
                (render-cell st)
                (flip-vertical
                 (triangle SIZE-T "solid" "black")))
   (+ (/ W 2) (/ (image-width head-cell) 2))
   (- (/ H 2) (* 2 CELL-HEIGHT))
   "middle" "top"
   (place-image/align
    (beside* (map render-cell (tape-tser t)))
    (/ W 2) (/ H 2)
    "right" "top"
    (place-image/align
     (beside/align "bottom"
                   head-cell
                   (beside* (map render-cell (tape-rest t))))
     (/ W 2) (/ H 2)
     "left" "top"
     (empty-scene W H)))))

(struct browse (play? l r))
(define (browse-draw b)
  (draw-state (first (browse-r b))))
(define (browse-step b)
  (match-define (browse play? l r) b)
  (if (browse-play? b)
    (browse-step-right b)
    b))
(define (browse-step-right b)
  (match-define (browse play? l r) b)
  (match r
    [(cons x (and nr (cons _ _)))
     (browse play? (cons x l) nr)]
    [_
     b]))
(define (browse-step-left b)
  (match-define (browse play? l r) b)
  (match l
    [(cons x nl)
     (browse play? nl (cons x r))]
    [_
     b]))
(define (browse-key b ke)
  (define nb
    (struct-copy browse b [play? #f]))
  (match ke
    ["left"
     (browse-step-left nb)]
    ["right"
     (browse-step-right nb)]
    [" "
     (struct-copy browse b [play? (not (browse-play? b))])]
    [_ b]))

(define (render tm input)
  (define l empty)
  (run* tm input #:inform (λ (i s) (set! l (cons s l))))
  (big-bang
   (browse #f empty (reverse l))
   ;; (browse #f (rest l) (list (first l)))
   [on-draw browse-draw]
   [on-tick browse-step 1/10]
   [on-key browse-key]))

(module+ test
  (when #f
    (render implicit-binary-add
            '(0 1 1 0 + 0 0 1 1))))

(module+ test
  (define implicit-binary-add-mt
    (implicit-tm
     [no-carry
      [(0 0) (no-carry 0 R)]
      [(1 0) (no-carry 1 R)]
      [(0 1) (no-carry 1 R)]
      [(1 1) (   carry 0 R)]
      [    _ (    HALT _ L)]]
     [carry
      [(0 0) (no-carry 1 R)]
      [(0 1) (   carry 0 R)]
      [(1 0) (   carry 0 R)]
      [(1 1) (   carry 1 R)]
      [    _ (    HALT 1 R)]]))

  ;; 2 + 3 = 5
  (check-equal?
   (run* implicit-binary-add-mt
         '((0 1) (1 1) (0 0) (0 0))
         #:inform (make-display-state implicit-binary-add-mt))
   '(1 0 1 0))

  (when #f
    (render implicit-binary-add-mt
            '((0 1) (1 1) (0 0) (0 0)))))

(define-syntax-rule (define-tm-action right!)
  (define-syntax (right! stx)
    (raise-syntax-error 'right! "Illegal outside program-tm" stx)))

(define-syntax-rule (define-tm-action* i ...)
  (begin (define-tm-action i) ...))

(define-tm-action* right! left! write! halt!)

(begin-for-syntax
  (require racket/dict
           racket/list
           racket/syntax
           syntax/id-table)

  (define (sym-tree->list sym)
    (remove-duplicates
     (map syntax-e (flatten sym))))

  (define empty-env (make-immutable-free-id-table))
  (define-syntax-class (ptm-e current-state env)
    #:attributes (state0 (sym 1) (state 1) (delta 1))
    #:literals (let case read right! left! write! halt!)
    [pattern (let loop:id ()
               (~var body (ptm-e #'loop (dict-set env #'loop #t))))
             #:attr (sym 1) (attribute body.sym)
             #:attr (state 1) (cons #'loop (attribute body.state))
             #:attr state0 #'loop
             #:attr (delta 1) (attribute body.delta)]
    [pattern (case (read)
               [(opt0 opt1 ...) (~var body (ptm-e current-state env))]
               ...)
             #:attr (sym 1)
             (list* (attribute opt0)
                    (attribute opt1)
                    (attribute body.sym))
             #:attr (state 1) (attribute body.state)
             #:attr state0 current-state
             #:attr (delta 1)
             (append
              (for/list ([o0 (in-list (attribute opt0))]
                         [o1s (in-list (attribute opt1))]
                         [b (in-list (attribute body))])
                (list 'input (cons o0 o1s)))
              (attribute body.delta))]
    [pattern (left! (~var next (ptm-e current-state env)))
             #:attr (sym 1) (attribute next.sym)
             #:with this-state (generate-temporary 'left)
             #:attr (state 1) (cons #'this-state (attribute next.state))
             #:attr state0 #'this-state
             #:attr (delta 1)
             (λ (all-syms)
               (append
                (for/list ([a (in-list all-syms)])
                  #`[(this-state #,a) (next.state0 #,a L)])
                ((attribute next.delta) all-syms)))]
    ;; xxx remove code copying
    [pattern (right! (~var next (ptm-e current-state env)))
             #:attr (sym 1) (attribute next.sym)
             #:with this-state (generate-temporary 'right)
             #:attr (state 1) (cons #'this-state (attribute next.state))
             #:attr state0 #'this-state
             #:attr (delta 1)
             (λ (all-syms)
               (append
                (for/list ([a (in-list all-syms)])
                  #`[(this-state #,a) (next.state0 #,a R)])
                ((attribute next.delta) all-syms)))]
    [pattern (write! wsym:expr (~var next (ptm-e current-state env)))
             #:attr (sym 1) (cons #'wsym (attribute next.sym))
             #:with this-state (generate-temporary 'write)
             #:attr (state 1) (cons #'this-state (attribute next.state))
             #:attr state0 #'this-state
             #:attr (delta 1)
             (λ (all-syms)
               (append
                (for/list ([a (in-list all-syms)])
                  #`[(this-state #,a) (next.state0 wsym L)])
                ((attribute next.delta) all-syms)))]
    [pattern (halt!)
             #:attr (sym 1) empty
             #:attr (state 1) empty
             #:attr state0 #'HALT
             #:attr (delta 1)
             (λ (all-syms)
               empty)]
    [pattern (x:id)
             #:attr (sym 1) empty
             #:attr (state 1) empty
             #:attr state0 current-state
             #:fail-unless (dict-ref env #'x #f)
             "defined function"
             #:attr (delta 1) empty]))

(require racket/pretty)
(define-syntax (program-tm stx)
  (syntax-parse stx
    [(_ (~var e (ptm-e #f empty-env)))
     (define all-syms
       (sym-tree->list (cons #'_ (attribute e.sym))))
     (with-syntax ([(sym ...)
                    (remove '_ all-syms)]
                   [(state ...)
                    (flatten (attribute e.state))]
                   [(delta ...)
                    ((attribute e.delta) all-syms)])
       (syntax/loc stx
         (begin
           (pretty-print
            '(tm #:Q (state ... HALT)
                 #:G (sym ... _)
                 #:b _
                 #:S (sym ...)
                 #:q0 e.state0
                 #:F (HALT)
                 #:delta delta ...))
           (tm #:Q (state ... HALT)
               #:G (sym ... _)
               #:b _
               #:S (sym ...)
               #:q0 e.state0
               #:F (HALT)
               #:delta delta ...))))]))

(module+ test
  (check-match (program-tm (halt!))
               (*tm 'HALT (list 'HALT) (list)
                    '_ (hash-table ('HALT #t))
                    (hash-table)))
  (check-match (program-tm (write! 0 (halt!)))
               (*tm write-st (list write-st 'HALT) (list '0)
                    '_ (hash-table ['HALT #t]) ht)
               (begin
                 (and (equal? (hash-ref ht (cons write-st '0))
                              (list 'HALT '0 'L))
                      (equal? (hash-ref ht (cons write-st '_))
                              (list 'HALT '0 'L)))))
  (check-match (program-tm (right! (halt!)))
               (*tm right-st (list right-st 'HALT) (list)
                    '_ (hash-table ['HALT #t]) ht)
               (begin
                 (and (equal? (hash-ref ht (cons right-st '_))
                              (list 'HALT '_ 'R)))))
  (check-match (program-tm (left! (halt!)))
               (*tm right-st (list right-st 'HALT) (list)
                    '_ (hash-table ['HALT #t]) ht)
               (begin
                 (and (equal? (hash-ref ht (cons right-st '_))
                              (list 'HALT '_ 'L)))))

  ;; xxx This is where it stops working. Basically, the write! should
  ;; see the left! inside of it and use that to determine the
  ;; direction to go in, rather than always assuming it goes left. So
  ;; it merges the two commands together. I can either recognize this
  ;; statically or I can make a dynamic protocol in the delta
  ;; generators. I think the dyn proto would be better, but I can see
  ;; it breaking with loops.
  '
  (check-match (program-tm (write! 0 (left! (halt!))))
               (*tm write-st (list write-st 'HALT) (list '0)
                    '_ (hash-table ['HALT #t]) ht)
               (begin
                 (and (equal? (hash-ref ht (cons write-st '0))
                              (list 'HALT '0 'L))
                      (equal? (hash-ref ht (cons write-st '_))
                              (list 'HALT '0 'L)))))

  '
  (define program-binary-add1
    (program-tm
     (let main ()
       (case (read)
         [(0 1)
          (right!
           (main))]
         [(_)
          (left!
           (let add1 ()
             (case (read)
               [(1)
                (write! 0 (left! (add1)))]
               [(_ 0)
                (write! 1 (halt!))])))]))))
  '
  (check-equal?
   (run* program-binary-add1
         '(0 0 1 0)
         #:inform (make-display-state program-binary-add1))
   '(0 0 1 1)))
