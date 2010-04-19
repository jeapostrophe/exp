(module linear mzscheme
  (require (lib "plt-match.ss")
           (lib "list.ss")
           (lib "etc.ss")
           (lib "pretty.ss"))
  
  (define-struct atom () (make-inspector))
  (define-struct (atom:var atom) (mult id) (make-inspector))
  (define-struct (atom:int atom) (int) (make-inspector))
  
  (define-struct simple-expr () (make-inspector))
  (define-struct (simple-expr:+ simple-expr) (args) (make-inspector))
  (define-struct (simple-expr:- simple-expr) (arg1 arg2) (make-inspector))
  
  (define parse-simple-expr
    (match-lambda
      [`(+ ,a1 ,a2)
        (make-simple-expr:+
         (list
          (parse-simple-expr a1)
          (parse-simple-expr a2)))]
      [`(- ,a1 ,a2)
        (make-simple-expr:-
         (parse-simple-expr a1)
         (parse-simple-expr a2))]
      [`(* ,(? number? n) ,(? symbol? v))
        (make-atom:var n v)]
      [(? number? n)
       (make-atom:int n)]
      [(? symbol? v)
       (make-atom:var 1 v)]))
  
  (define simple-expr->sexp
    (match-lambda
      [(struct simple-expr:+ (lst))
       `(+ ,@(map simple-expr->sexp lst))]
      [(struct simple-expr:- (a1 a2))
       `(- ,(simple-expr->sexp a1) ,(simple-expr->sexp a2))]
      [(struct atom:var (n i))
       (if (eq? 1 n)
           i
           `(* ,n ,i))]
      [(struct atom:int (n))
       n]))
  
  (define simplify-simple-expr
    (match-lambda
      [(struct simple-expr:+ (lst))
       (make-simple-expr:+
        (foldl (lambda (t a)
                 (if (simple-expr:+? t)
                     (append (simple-expr:+-args (simplify-simple-expr t)) a)
                     (list* t a)))
               empty
               lst))]
      [(struct simple-expr:- (a1 a2))
       (make-simple-expr:- a1 a2)]
      [(struct atom:var (n i))
       (make-atom:var n i)]
      [(struct atom:int (n))
       (make-atom:int n)]))
  
  (define-struct simple-eq () (make-inspector))
  (define-struct (simple-eq:eq simple-eq) (left right) (make-inspector))
  (define-struct (simple-eq:ne simple-eq) (left right) (make-inspector))
  (define-struct (simple-eq:lt simple-eq) (left right) (make-inspector))
  (define-struct (simple-eq:gt simple-eq) (left right) (make-inspector))
  (define-struct (simple-eq:lte simple-eq) (left right) (make-inspector))
  (define-struct (simple-eq:gte simple-eq) (left right) (make-inspector))
  
  (define-struct ele () (make-inspector))
  (define-struct (ele:and ele) (left right) (make-inspector))
  (define-struct (ele:or ele) (left right) (make-inspector))
  (define-struct (ele:not ele) (term) (make-inspector))
  
  (define-struct standard-eq () (make-inspector))
  (define-struct (standard-eq:lte standard-eq) (left right) (make-inspector))
  (define-struct (standard-eq:gte standard-eq) (left right) (make-inspector))
  
  (define-struct le () (make-inspector))
  (define-struct (le:and le) (parts) (make-inspector))
  
  (define simplify-le
    (match-lambda
      [(struct le:and (lst))
       (make-le:and
        (foldl (lambda (t a)
                 (if (le:and? t)
                     (append (le:and-parts t) a)
                     (list* t a)))
               empty
               (map simplify-le lst)))]
       [(struct standard-eq:lte (l r))
        (make-standard-eq:lte (simplify-simple-expr l) (simplify-simple-expr r))]
       [(struct standard-eq:gte (l r))
        (make-standard-eq:gte (simplify-simple-expr l) (simplify-simple-expr r))]))
  
  (define le->sexp
    (match-lambda
      [(struct le:and (lst))
       `(and ,@(map le->sexp lst))]
      [(struct standard-eq:lte (l r))
       `(<= ,(simple-expr->sexp l) ,(simple-expr->sexp r))]
      [(struct standard-eq:gte (l r))
       `(>= ,(simple-expr->sexp l) ,(simple-expr->sexp r))]))  
  
  (define parse-ele
    (match-lambda
      [`(not ,term)
        (make-ele:not (parse-ele term))]
      [`(and ,left ,right)
        (make-ele:and (parse-ele left)
                      (parse-ele right))]
      [`(or ,left ,right)
        (make-ele:or (parse-ele left)
                     (parse-ele right))]
      [`(= ,left ,right)
        (make-simple-eq:eq (parse-simple-expr left)
                           (parse-simple-expr right))]
      [`(!= ,left ,right)
        (make-simple-eq:ne (parse-simple-expr left)
                           (parse-simple-expr right))]
      [`(< ,left ,right)
        (make-simple-eq:lt (parse-simple-expr left)
                           (parse-simple-expr right))]
      [`(> ,left ,right)
        (make-simple-eq:gt (parse-simple-expr left)
                           (parse-simple-expr right))]
      [`(=< ,left ,right)
        (make-simple-eq:lte (parse-simple-expr left)
                            (parse-simple-expr right))]
      [`(>= ,left ,right)
        (make-simple-eq:gte (parse-simple-expr left)
                            (parse-simple-expr right))]))
  
  (define (ele->le term on off)
    (define (add-M t)
      (foldl (lambda (v a)
               (make-simple-expr:+ (list a (make-atom:var 'M v))))
             (foldl (lambda (v a)
                      (make-simple-expr:+ 
                       (list
                        a
                        (make-simple-expr:-
                         (make-atom:int 'M)
                         (make-atom:var 'M v)))))
                    t
                    off)
             on))
    (match term
      [(struct ele:and (l r))
       (make-le:and 
        (list
         (ele->le l on off)
         (ele->le r on off)))]
      [(struct ele:or (l r))
       (let ([new (gensym 'b)])
         (make-le:and
          (list
           (ele->le l (list* new on) off)
           (ele->le r on (list* new off)))))]
      [(struct ele:not ((struct ele:and (l r))))
       (ele->le
        (make-ele:or (make-ele:not l) (make-ele:not r))
        on off)]
      [(struct ele:not ((struct ele:or (l r))))
       (ele->le
        (make-ele:and (make-ele:not l) (make-ele:not r))
        on off)]
      [(struct ele:not ((struct ele:not (t))))
       (ele->le t on off)]
      [(struct ele:not ((struct simple-eq:eq (l r))))
       (ele->le (make-simple-eq:ne l r) on off)]
      [(struct ele:not ((struct simple-eq:ne (l r))))
       (ele->le (make-simple-eq:eq l r) on off)]
      [(struct ele:not ((struct simple-eq:lt (l r))))
       (ele->le (make-simple-eq:gte l r) on off)]
      [(struct ele:not ((struct simple-eq:gt (l r))))
       (ele->le (make-simple-eq:lte l r) on off)]
      [(struct ele:not ((struct simple-eq:lte (l r))))
       (ele->le (make-simple-eq:gt l r) on off)]
      [(struct ele:not ((struct simple-eq:gte (l r))))
       (ele->le (make-simple-eq:lt l r) on off)]
      [(struct simple-eq:eq (l r))
       (make-le:and
        (list
         (ele->le (make-simple-eq:lte l r) on off)
         (ele->le (make-simple-eq:gte l r) on off)))]
      [(struct simple-eq:ne (l r))
       (ele->le
        (make-ele:or (make-simple-eq:lt l r)
                     (make-simple-eq:gt l r))
        on off)]
      [(struct simple-eq:lt (l r))
       (ele->le
        (make-simple-eq:lte l (make-simple-expr:- r (make-atom:int 1)))
        on off)]                            
      [(struct simple-eq:gt (l r))
       (ele->le
        (make-simple-eq:gte l (make-simple-expr:+ (list r (make-atom:int 1))))
        on off)]
      [(struct simple-eq:lte (l r))
       (make-standard-eq:lte l (add-M r))]
      [(struct simple-eq:gte (l r))
       (make-standard-eq:gte (add-M l) r)]))
  
  (define (convert sexp)
    (le->sexp (simplify-le (ele->le (parse-ele sexp) empty empty))))
  
  (define (test)
    (let ([term
           `(and (or (or (or (= x1 (+ s 1))
                             (= x2 (+ s 1)))
                         (or (= x3 (+ s 1))
                             (= x4 (+ s 1))))
                     (or (or (= x5 (+ s 1))
                             (= x6 (+ s 1)))
                         (or (= x7 (+ s 1))
                             (= x8 (+ s 1)))))
                 (or (or (or (= x1 (- s 1))
                             (= x2 (- s 1)))
                         (or (= x3 (- s 1))
                             (= x4 (- s 1))))
                     (or (or (= x5 (- s 1))
                             (= x6 (- s 1)))
                         (or (= x7 (- s 1))
                             (= x8 (- s 1))))))])
      (pretty-print
       (convert term)))))