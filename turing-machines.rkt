#lang racket/base
(require (for-syntax racket/base
                     racket/list
                     syntax/parse)
         racket/function
         racket/match
         racket/list)

(define BOUND 400)

(define-syntax-rule (define-check id S)
  (define ((id where) s)
    (if (member s S)
      s
      (error 'id "~a: ~v not in ~v" where s S))))
(define-check check-LR '(L R))

(struct *tm (initial states inputs blank final? delta) #:transparent)
(define (tm #:Q Q #:G G #:b blank #:S inputs
            #:q0 initial-state #:F final-state
            #:delta delta)
  (define-check check-G G)
  (define-check check-Q Q)
  (*tm ((check-Q 'initial-state) initial-state)
       Q
       (map (check-G 'inputs) inputs)
       (if (member blank inputs)
         (error 'tm "Blank cannot be in input alphabet")
         ((check-G 'blank) blank))
       (for/hash ([fs (in-list final-state)])
         (values ((check-Q 'final-state) fs) #t))
       (for/hash ([d (in-list delta)])
         (match-define
          `[(,delta-state ,delta-symbol)
            (,next-state ,write-symbol ,head-movement)]
          d)
         (values
          (cons ((check-Q 'delta-state) delta-state)
                ((check-G 'delta-symbol) delta-symbol))
          (list ((check-Q 'next-state) next-state)
                ((check-G 'write-symbol) write-symbol)
                ((check-LR 'head-movement) head-movement))))))

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
  (run tm input BOUND #:inform inform-f))

(require racket/format
         racket/string)
(define (make-display-state tm)
  (define max-st-len
    (apply max
           (map (compose string-length ~a)
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
    (tm #:Q '(A B C HALT)
        #:G '(0 1)
        #:b '0
        #:S '(1)
        #:q0 'A
        #:F '(HALT)
        #:delta
        '([(A 0) (   B 1 R)]
          [(A 1) (   C 1 L)]
          [(B 0) (   A 1 L)]
          [(B 1) (   B 1 R)]
          [(C 0) (   B 1 L)]
          [(C 1) (HALT 1 R)])))

  (check-equal?
   (run* busy-beaver
         '()
         #:inform (make-display-state busy-beaver))
   '(1 1 1 1 1 1))

  (define unary-addition
    (tm #:Q '(consume-first-number
              consume-second-number
              override-last-*
              seek-beginning
              HALT)
        #:G '(* _ /)
        #:b '_
        #:S '(* /)
        #:q0 'consume-first-number
        #:F '(HALT)
        #:delta
        '([(consume-first-number *)
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
           (HALT _ R)])))

  (check-equal?
   (run* unary-addition
         '(* * * * * / * * * * *)
         #:inform (make-display-state unary-addition))
   '(* * * * * * * * * *)))

(define (implicit-tm implicit-delta)
  (when (empty? implicit-delta)
    (error 'implicit-tm "Requires at least one state"))
  (match-define
   `([,idelta-state
      [,idelta-symbol
       (,inext-state ,iwrite-symbol ,ihead-movement)]
      ...]
     ...)
   implicit-delta)
  (tm #:Q
      (remove-duplicates
       (cons 'HALT
             (append* idelta-state
                      inext-state)))
      #:G
      (remove-duplicates
       (cons '_
             (append (append* idelta-symbol)
                     (append* iwrite-symbol))))
      #:b '_
      #:S (remove '_ (remove-duplicates (append* idelta-symbol)))
      #:q0 (first idelta-state)
      #:F '(HALT)
      #:delta
      (append*
       (for/list ([delta-state (in-list idelta-state)]
                  [ids (in-list idelta-symbol)]
                  [ins (in-list inext-state)]
                  [iws (in-list iwrite-symbol)]
                  [ihm (in-list ihead-movement)])
         (for/list ([delta-symbol (in-list ids)]
                    [next-state (in-list ins)]
                    [write-symbol (in-list iws)]
                    [head-movement (in-list ihm)])
           `[(,delta-state ,delta-symbol)
             (,next-state ,write-symbol ,head-movement)])))))

(module+ test
  (define implicit-unary-addition
    (implicit-tm
     '([consume-first-number
        [* (consume-first-number * R)]
        [+ (consume-second-number * R)]]
       [consume-second-number
        [* (consume-second-number * R)]
        [_ (override-last-* _ L)]]
       [override-last-*
        [* (seek-beginning _ L)]]
       [seek-beginning
        [* (seek-beginning * L)]
        [_ (HALT _ R)]])))

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
     '([find-end
        [0 (find-end 0 R)]
        [1 (find-end 1 R)]
        [_ (zero-until-0 _ L)]]
       [zero-until-0
        [1 (zero-until-0 0 L)]
        [0 (HALT 1 L)]])))

  (check-equal?
   (run* implicit-binary-add1
         '(0 0 1 0)
         #:inform (make-display-state implicit-binary-add1))
   '(0 0 1 1))

  (define implicit-binary-sub1
    (implicit-tm
     '([ones-complement
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
        [_ (HALT _ R)]])))

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
     '([check-if-zero
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
        [_ (HALT _ R)]])))

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
     '([no-carry
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
        [    _ (    HALT 1 R)]])))

  ;; 2 + 3 = 5
  (check-equal?
   (run* implicit-binary-add-mt
         '((0 1) (1 1) (0 0) (0 0))
         #:inform (make-display-state implicit-binary-add-mt))
   '(1 0 1 0))

  (when #f
    (render implicit-binary-add-mt
            '((0 1) (1 1) (0 0) (0 0)))))

(struct *itm (delta))
(define (itm . d) (*ptm d))
(define (itm->tm it #:and-then [and-then empty])
  (match-define (*itm i) it)
  (define all-syms
    (remove-duplicates
     (cons '_
           (append (map second i)
                   (map fourth i)
                   and-then))))
  (tm #:Q
      (remove-duplicates
       (cons 'HALT
             (append (map first i)
                     (map third i))))
      #:G all-syms
      #:b '_
      #:S (remove '_ all-syms)
      #:q0 (first (first i))
      #:F '(HALT)
      #:delta
      (for/list ([i (in-list i)])
        (match-define (list state input goto output head) i)
        (list (list state input) (list goto output head)))))

(struct *ptm (pdelta))
(define (ptm . pd) (*ptm pd))
(define tm:else (gensym 'else))
(define (ptm->itm pt #:and-then [and-then empty])
  (match-define (*ptm pd) pt)
  (define all-syms
    (remove tm:else
            (remove-duplicates
             (cons '_
                   (append (map second pd)
                           (map fourth pd)
                           and-then)))))
  (*itm
   (append*
    (for/list ([i (in-list pd)])
      (match-define (list state input goto output head) i)
      (cond
        [(eq? tm:else input)
         (define state-sym
           (append-map (λ (s)
                         (if (eq? (first s) state)
                           (list (second s))
                           empty))
                       pd))
         (for/list ([s (in-list (remove* state-sym all-syms))])
           (list state s goto
                 (if (eq? tm:else output)
                   s
                   output)
                 head))]
        [(eq? tm:else output)
         (error 'ptm->itm
                "tm:else not allowed in output unless input is also tm:else")]
        [else
         (list i)])))))

(define (compile-ptm t #:and-then [and-then empty])
  (define it (ptm->itm t #:and-then and-then))
  (itm->tm it #:and-then and-then))

(module+ test
  (define-syntax-rule (check-tm tm input output)
    (let ([tmv tm])
      (check-equal?
       (run* tmv input #:inform (make-display-state tmv))
       output)))
  (define-syntax-rule (check-ptm tm input output)
    (let ([inputv input])
      (check-tm (compile-ptm tm #:and-then inputv) inputv output))))

;; xxx should i add that these 'read' to their name?

(define (tm:write&move state input goto output head)
  (ptm (list state input goto output head)))
(module+ test
  (check-ptm (tm:write&move 'start 'X 'HALT 'Y 'R)
             '(X Y Z)
             '(Y Y Z)))

(define (tm:combine . ps)
  (match-define (list (*ptm pd) ...) ps)
  (*ptm (append* pd)))
(module+ test
  (check-ptm (tm:combine (tm:write&move 'start 'X 'HALT 'Y 'R))
             '(X Y Z)
             '(Y Y Z))
  (check-ptm (tm:combine (tm:write&move 0 'X 1 'Y 'R)
                         (tm:write&move 1 'Y 'HALT 'X 'R))
             '(X Y Z)
             '(Y X Z)))

(define (tm:write&left state input goto output)
  (tm:write&move state input goto output 'L))
(define (tm:write&right state input goto output)
  (tm:write&move state input goto output 'R))
(module+ test
  (check-ptm (tm:combine (tm:write&left 0 'X 1 'Y)
                         (tm:write&right 1 '_ 'HALT 'X))
             '(X Y Z)
             '(X Y Y Z)))

(define (tm:move state goto head)
  (tm:write&move state tm:else goto tm:else head))
(define (tm:left state goto)
  (tm:move state goto 'L))
(define (tm:right state goto)
  (tm:move state goto 'R))
(module+ test
  (check-ptm (tm:combine (tm:right 0 1)
                         (tm:right 1 2)
                         (tm:write&left 2 tm:else 'HALT 'fin))
             '(X Y Z)
             '(X Y fin)))

(define current-state-prefix (make-parameter empty))
(define (snoc l x)
  (append l (list x)))

(define next-state 0)
(define (state-format i)
  (set! next-state (add1 next-state))
  (cons next-state (snoc (current-state-prefix) i)))
(define-syntax-rule (with-states label (s ...) body)
  (parameterize ([current-state-prefix
                  (snoc (current-state-prefix) label)])
    (let ([s (state-format 's)]
          ...)
      body)))

;; This is interesting because it leaves the tape and head unchanged.
(define (tm:halt state)
  (with-states "halt" (tmp)
    (tm:combine (tm:left state tmp)
                (tm:right tmp 'HALT))))
(module+ test
  (check-ptm (tm:halt 'start)
             '(X Y Z)
             '(X Y Z)))

(define (tm:goto state input goto)
  (with-states "goto" (tmp)
    (tm:combine (tm:write&right state input tmp input)
                (tm:left tmp goto))))

(define (tm:write state output goto)
  (with-states "write" (tmp)
    (tm:combine (tm:write&left state tm:else tmp output)
                (tm:right tmp goto))))
(define (tm:right-until state stop-input goto)
  (tm:combine (tm:goto state stop-input goto)
              (tm:right state state)))
(define (tm:write&left-until state output stop-input goto)
  (tm:combine (tm:goto state stop-input goto)
              (tm:write&left state tm:else state output)))

(module+ test
  (define program-binary-add1
    (compile-ptm
     (with-states "binary-add1" (main pre-add1 find-last-zero write-1)
       (tm:combine
        (tm:right-until main '_ pre-add1)
        (tm:left pre-add1 find-last-zero)
        (tm:write&left-until find-last-zero '0 '0 write-1)
        (tm:write write-1 '1 'HALT)))))

  (check-tm program-binary-add1
            '(0 0 1 0)
            '(0 0 1 1)))

(define (tm:right* state how-many goto)
  (if (zero? how-many)
    (tm:goto state tm:else goto)
    (with-states (format "right*(~a)" how-many) (tmp)
      (tm:combine (tm:right state tmp)
                  (tm:right* tmp (sub1 how-many) goto)))))

(define (tm:read-from state possible-syms generator)
  (apply
   tm:combine
   (for/list ([sym (in-list possible-syms)])
     (with-states (format "read-from(~a)" sym) (sym-state)
       (tm:combine (tm:goto state sym sym-state)
                   (generator sym sym-state))))))

(define (tm:right-stop-when state end-sym goto)
  (with-states "right-stop-when" (tmp)
    (tm:combine (tm:right-until state end-sym tmp)
                (tm:left tmp goto))))

(require racket/system)
(define (draw-ptm! ptm f)
  (match-define (*ptm pd) ptm)
  (with-output-to-file f
    #:exists 'replace
    (λ ()
      (printf "strict digraph {\n")
      
      (struct obj (children more))
      (define (new-obj)
        (obj (box empty) (make-hash)))
      (define (store! o path e)
        (match path
          [(cons f sub-path)
           (hash-update! (obj-more o) f
                         (λ (msub-o)
                           (define sub-o
                             (or msub-o
                                 (new-obj)))
                           (store! sub-o sub-path e)
                           sub-o)
                         #f)]
          [_
           (define b (obj-children o))
           (set-box! b (cons e (unbox b)))]))

      (define consolidate1
        (match-lambda
         [(regexp #"^read-from" (list _))
          "read-from"]
         [(regexp #"^lhs" (list _))
          "lhs"]
         [(regexp #"^rhs" (list _))
          "rhs"]
         [x x]))
      (define (consolidate p)
        (if (list? p)
          (map consolidate1 p)
          p))

      (define (cdr* x)
        (if (cons? x) (cdr x) x))
      (define (car* x)
        (if (cons? x) (car x) x))

      (define top (new-obj))      
      (for ([p (in-list pd)])
        (match-define (list state input goto output head) p)
        (store! top 
                (consolidate (cdr state))
                (list (consolidate (cdr state)) input 
                      (consolidate (cdr* goto))
                      output head)))

      (define (print-obj o)
        (match-define (obj (box children) path->o) o)
        (for ([p (in-list children)])
          (match-define (list state input goto output head) p)
          (printf "~s -> ~s\n" (~a (cdr* state)) (~a (cdr* goto))))
        (for ([(k o) (in-hash path->o)])
          (printf "subgraph ~s {\n" (~a k))
          (print-obj o)
          (printf "}\n")))
      (print-obj top)

      (printf "}")))
  (system* "/usr/bin/dot"
           "-Tpdf"
           f
           "-o"
           (path-replace-suffix f #".pdf")))

(module+ test
  (define-syntax-rule (check-tms tm is os)
    (check-tm tm (string->list is) (string->list os)))

  (define numbers (string->list "0123456789"))

  ;; xxx first mark the lhs/rhs
  
  ;; xxx then, add them and write the answer to the right of the rhs
  ;; while moving the marks

  ;; xxx then check the marks and see if they are on numbers and if
  ;; not clear everything from the rhs mark to the left (
  (define itm-dec-add
    (with-states "dec-add" (main op seek-lhs lhs)
      (tm:combine
       (tm:right-stop-when main #\space op)
       (tm:read-from
        op (string->list "+")
        (λ (op op-state)
          (match op
            [#\+
             ;; xxx skip over more spaces than 1?
             (tm:combine
              (tm:right* op-state 2 seek-lhs)
              (tm:right-stop-when seek-lhs #\space lhs)
              (tm:read-from
               lhs numbers
               (λ (lhs lhs-state)
                 (with-states (format "lhs(~a)" lhs) (seek-rhs rhs)
                   (tm:combine
                    (tm:right-stop-when lhs-state #\) rhs)
                    (tm:read-from
                     rhs numbers
                     (λ (rhs rhs-state)
                       (with-states (format "rhs(~a)" rhs)
                           (tmp1 tmp2 write-ans write-ans2 reset-head)
                         (tm:combine
                          (tm:right rhs-state tmp1)
                          (tm:write tmp1 '_ tmp2)
                          (tm:write&left-until tmp2 '_ #\( write-ans)
                          (match (string->list
                                  (number->string
                                   (+ (string->number (string lhs))
                                      (string->number (string rhs)))))
                            [(list ans)
                             (tm:write write-ans ans 'HALT)]
                            [(list #\1 ans)
                             (tm:combine
                              (tm:write&right write-ans tm:else write-ans2 #\1)
                              (tm:write write-ans2 ans reset-head)
                              (tm:left reset-head 'HALT))]))))))))))]))))))

  (when #f
    (draw-ptm! itm-dec-add "/home/jay/Downloads/dec-add.dot"))

  (define program-dec-add
    (compile-ptm
     #:and-then (string->list "()+ ")
     itm-dec-add))

  (define-syntax-rule (check-add i o)
    (check-tms program-dec-add i o))

  ;; Single digit
  (check-add "(+ 2 1)"
             "3")
  ;; Single digit + carry
  (check-add "(+ 9 2)"
             "11")
  (check-add "(+ 9 9)"
             "18")

  (exit 0)

  ;; xxx would it be better to be like a stack machine/forth?

  ;; Multi-digit
  (check-add "(+ 12 34)"
             "46")
  ;; Multi-digit + carry
  (check-add "(+ 16 16)"
             "32")
  ;; Multi-digit + carry + expand
  (check-add "(+ 20 90)"
             "110")

  (check-add "(+ (+ 10 10) 90)"
             "110"))
