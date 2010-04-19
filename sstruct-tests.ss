#lang scheme
(require tests/eli-tester
         scheme/struct-info
         "sstruct.ss")

(test
 (local [(define-sstruct a ())]
   (test 
    ; Constructors exist
    (a)
    ; Predicates exist
    (a? (a))
    ; Match works
    (match (a)
      [(a)
       #t])
    =>
    #t))
 
 (define-sstruct a () #:omit-define-syntaxes #:omit-define-syntaxes) =error> "redundant #:omit-define-syntaxes specification in struct"
 (define-sstruct a () #:omit-define-values #:omit-define-values) =error> "redundant #:omit-define-values specification in struct"
 (define-sstruct a () #:mutable #:mutable) =error> "redundant #:mutable specification in struct"
 (define-sstruct a () #:guard #f #:guard #f) =error> "too many #:guard specifications in struct"
 
 (local [(define-sstruct a ())]
   (define-sstruct b () #:super a #:super a))
 =error> "too many #:super specifications in struct"
 (define-sstruct b () #:super 1) =error> "expected identifier"
 (local [(define-sstruct a ())]
   (define-sstruct (b a) () #:super a))
 =error> "redundant #:super specification in struct"
 
 (define-sstruct a () #:constructor make-a #:constructor gimme-an-a) =error> "too many #:constructor specifications in struct"
 (define-sstruct a () #:predicate a?? #:predicate a???) =error> "too many #:predicate specifications in struct"
 (define-sstruct a () #:inspector #f #:inspector #f) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 (define-sstruct a () #:transparent #:transparent) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 (define-sstruct a () #:prefab #:prefab) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 (define-sstruct a () #:inspector #f #:transparent) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 (define-sstruct a () #:inspector #f #:prefab) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 (define-sstruct a () #:transparent #:prefab) =error> "too many #:inspector, #:transparent, #:prefab specifications in struct"
 
 (define-sstruct a (x x)) =error> "duplicate field identifier"
 (define-sstruct 4 ()) =error> "identifier"
 (define-sstruct (a b c) ()) =error> "struct description"
 (define-sstruct (a 5) ()) =error> "identifier"
 (define-sstruct a (5)) =error> "expected keyword or expected field specification"
 (define-sstruct a (#:x 5)) =error> "expected field specification"
 (define-sstruct a ([5 x])) =error> "expected identifier"
 (define-sstruct a ([#:x x])) =error> "expected identifier"
 (define-sstruct a ([x #:mutable #:mutable])) =error> "redundant #:mutable specification in field"
 (define-sstruct a ([x #:accessor 5])) =error> "identifier"
 (define-sstruct a ([x #:accessor gimme-an-x #:accessor x-please])) =error> "too many #:accessor specifications in field"
 (define-sstruct a ([x #:mutator set-an-x! #:mutator x!])) =error> "too many #:mutator specifications in field"
 (define-sstruct a ([x 5 6])) =error> "too many default value specifications in field"
 
 ; Compatible with match's struct expander
 (local [(define-sstruct a (x))]
   (test
    (match (a 5)
      [(struct a (x))
       x])
    =>
    5))
 
 ; Compatible with define-struct for parent hood
 (local [(define-sstruct a ())
         (define-struct (b a) ())]
   (test 
    (a? (make-b))))
 ; But defaults must be supplied always
 (local [(define-sstruct a ([x 5]))
         (define-struct (b a) ())]
   (test 
    (a? (a))
    (make-b) =error> "expects 1 argument"))
 ; And keywords are passed by position
 (local [(define-sstruct a (#:x x y))
         (define-struct (b a) ())]
   (test 
    (a-x (a 5 #:x 6)) => 6
    (a-x (a #:x 6 5)) => 6
    (a-x (make-b 6 5)) => 6))
 
 (local [(define-sstruct a ())
         (define-sstruct (b a) ())]
   (test 
    ; Super types work
    (a? (b))
    ; in match too
    (match (b)
      [(a)
       #t])
    =>
    #t)) 
 
 (local [(define-sstruct a ())
         (define-sstruct b () #:super a)]
   (test 
    ; Super types work
    (a? (b))
    ; in match too
    (match (b)
      [(a)
       #t])
    =>
    #t))
 
 ; You can override the constructor
 (local [(define-sstruct a ()
           #:constructor make-a)]
   (test
    (a? (make-a))
    ; And match still works
    (match (make-a)
      [(make-a)
       #t])
    =>
    #t))
 
 ; You can override the predicate
 (local [(define-sstruct a ()
           #:predicate an-a?)]
   (test
    a? =error> "unbound"
    (an-a? (a))
    ; Match still works
    (match (a)
      [(a)
       #t])
    =>
    #t))
 
 ; Properties
 (local [(define-sstruct a ()
           #:property prop:procedure
           (lambda (the-a . args)
             args))]
   (test
    ((a) 5) => (list 5)))
 
 ; Prefab
 (local [(define-sstruct a ()
           #:prefab)]
   (test
    (prefab-struct-key (a)) => 'a))
 
 ; Guards
 (local [(define-sstruct a (x)
           #:guard (lambda (x name)
                     (if (x . > . 5)
                         (values 5)
                         (values x))))]
   (test (a-x (a 2)) => 2
         (a-x (a 5)) => 5
         (a-x (a 7)) => 5))
 
 ; Prefabs can't have properties or guards
 (define-sstruct a ()
   #:prefab
   #:property prop:procedure
   (lambda (the-a . args)
     args))
 =error> "cannot use #:property specification for prefab structure type"
 
 (define-sstruct a ()
   #:prefab
   #:guard (lambda (name) #t))
 =error> "cannot use #:guard specification for prefab structure type"
 
 (define-sstruct a ()
   #:inspector 'prefab
   #:guard (lambda (name) #t))
 =error> "cannot use #:guard specification for prefab structure type"
 
 ; Transparent
 (local [(define-sstruct a (x))
         (define-sstruct b (x) #:transparent)]
   (test (equal? (a 5) (a 5)) => #f
         (equal? (b 5) (b 5)) => #t
         (equal? (b 5) (b 6)) => #f))
 
 ; Inspector
 (local [(define some-inspector (make-sibling-inspector))
         (define another-inspector (make-inspector some-inspector))
         (define-syntax-rule (first-value e)
           (call-with-values (lambda () e)
                             (lambda (a . _) a)))
         (define-sstruct a ())
         (define-sstruct b () #:inspector another-inspector)]
   (test (first-value (struct-info (a))) => #f
         (first-value (struct-info (b))) => #f
         (first-value 
          (parameterize ([current-inspector some-inspector])
           (struct-info (b))))))
 
 (local [(define-sstruct a ()
           #:omit-define-syntaxes)]
   (test
    (a? (a))
    (match (a)
      [(a) #t])
    =error>
    "syntax error in pattern"))
 
 (local [(define-sstruct a ()
           #:omit-define-values)]
   (test
    a? =error> "unbound"
    a =error> "unbound"
    (match 5
      [(a) #f]
      [(? number?) #t])
    => #t))
 
 (local [(define-sstruct a (x))]
   (test (a-x (a 5)) => 5
         (match (a 5)
           [(a x) x])
         => 5))
 
 (local [(define-sstruct a ([x #:mutable]))
         (define an-a (a 5))]
   (test (a-x an-a) => 5
         (set-a-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a (x)
           #:mutable)
         (define an-a (a 5))]
   (test (a-x an-a) => 5
         (set-a-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a ([x #:accessor gimme-the-x]))]
   (test (gimme-the-x (a 5)) => 5
         (match (a 5)
           [(a x) x]) 
         => 5
         a-x =error> "unbound"))
 
 (define-sstruct a ([x #:mutator set-the-x!])) =error> "illegal #:mutator specification in immutable field"
 
 (define-sstruct a ([x #:mutable]) #:mutable) =error> "redundant #:mutable specification in field"
 
 (local [(define-sstruct a ([x #:mutable
                               #:mutator set-the-x!]))
         (define an-a (a 5))]
   (test (a-x an-a) => 5
         set-a-x! =error> "unbound"
         (set-the-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a ([x #:mutator set-the-x!])
           #:mutable)
         (define an-a (a 5))]
   (test (a-x an-a) => 5
         set-a-x! =error> "unbound"
         (set-the-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a (#:x x))]
   (test (a 5) =error> "#:x"
         (a #:x 5)
         (a-x (a #:x 5)) => 5
         (match (a #:x 5)
           [(a #:x x) x])
         =>
         5))
 
 (define-sstruct a (#:x x #:x y)) =error> "duplicate keyword"
 
 (local [(define-sstruct a (#:x y))]
   (test (a 5) =error> "#:x"
         (a #:x 5)
         (a-y (a #:x 5)) => 5
         (match (a #:x 5)
           [(a #:x x) x])
         =>
         5))
 
 (local [(define-sstruct a (#:x [x #:accessor gimme-the-x]))]
   (test (a 5) =error> "#:x"
         (a #:x 5)
         (gimme-the-x (a #:x 5)) => 5
         (match (a #:x 5)
           [(a #:x x) x])
         =>
         5))
 
 (local [(define-sstruct a (#:x x y))]
   (test (a 5) =error> "#:x"
         (a #:x 5 6)
         (a 6 #:x 5)
         (a-x (a 6 #:x 5)) => 5
         (a-y (a #:x 5 6)) => 6
         (match (a 6 #:x 5)
           [(a #:x x y) (values x y)])
         =>
         (values 5 6)
         (match (a 6 #:x 5)
           [(a y #:x x) (values x y)])
         =>
         (values 5 6)))
 
 (local [(define-sstruct a (#:x [x #:mutable]))
         (define an-a (a #:x 5))]
   (test (a-x an-a) => 5
         (set-a-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a (#:x [x #:mutable
                                   #:mutator set-the-x!]))
         (define an-a (a #:x 5))]
   (test (a-x an-a) => 5
         (set-the-x! an-a 6) => (void)
         (a-x an-a) => 6))
 
 (local [(define-sstruct a ([x 7]))]
   (test (a)
         (a-x (a)) => 7
         (a-x (a 5)) => 5))
 
 (local [(define-sstruct a (y [x (add1 y)]))]
   (test (a 1)
         (a-x (a 1)) => 2
         (a-x (a 5)) => 6))
 
 (local [(define-sstruct a (#:x x))]
   (test (with-output-to-string (λ () (printf "~S" (a #:x 5))))
         =>
         "#<a>"))
 (local [(define-sstruct a (#:x x) #:transparent)]
   (test (with-output-to-string (λ () (printf "~S" (a #:x 5))))
         =>
         "#(struct:a 5)"))
 
 (local [(define-sstruct parent (x))
         (define-sstruct (child parent) (x))]
   (test (parent-x (child 1 2)) => 1
         (child-x (child 1 2)) => 2))
 
 (local [(define-sstruct parent (#:x x))
         (define-sstruct (child parent) (#:x x))]
   #t)
 =error>
 "duplicate keyword"
 
 (local [(define-sstruct parent (#:x x))
         (define-sstruct (child parent) (#:y x))]
   (test (parent-x (child #:x 5 #:y 6)) => 5
         (child-x (child #:x 5 #:y 6)) => 6))
 
 (local [(define-sstruct parent (x #:y y z))
         (define-sstruct (child parent) (a b #:c c))
         (define child->vector
           (match-lambda
             [(child x #:y y z a b #:c c)
              (vector x y z a b c)]))]
   (test (child->vector (child 1 #:y 2 3 4 5 #:c 6))
         => (vector 1 2 3 4 5 6)
         (child->vector (child 1 3 4 #:y 2 5 #:c 6))
         => (vector 1 2 3 4 5 6)
         (child->vector (child #:c 6 1 3 4 #:y 2 5))
         => (vector 1 2 3 4 5 6)))
 
 )