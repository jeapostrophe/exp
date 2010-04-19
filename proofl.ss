(module proofl mzscheme
  (require (lib "list.ss")
           (lib "etc.ss")
           (lib "kw.ss")
           (lib "contract.ss")
           (lib "pretty.ss")
           (lib "plt-match.ss")
           (planet "list.ss" ("jaymccarthy" "mmss.plt" 1)))
  
  (define indent-level (make-parameter 0))  
  (define proof-level (make-parameter 2))
  
  (define (printf/indent f . args)
    (apply printf (string-append "~a" f)
           (list* (make-string (indent-level) #\tab)
                  args)))
  
  ;; Basic proofs
  (define wff?
    (match-lambda
      [`(neg ,a)
        (wff? a)]
      [`(,a -> ,b)
        (and (wff? a) (wff? b))]
      [(and x (? symbol?))
       #t]))
  
  (define-struct proof ())  
  ; Level 0
  (define-struct (proof:0 proof) ())
  (define-struct (proof:assume proof:0) (a))
  (define-struct (proof:mp proof:0) (sub1 sub2))
  (define-struct (proof:as:1 proof:0) (a b))
  (define-struct (proof:as:2 proof:0) (a b))
  (define-struct (proof:as:3 proof:0) (a b))
  (define-struct (proof:as:4 proof:0) (a b c))
  
  (define (proof->proof:0 p)
    (match p
      [(struct proof:0 ())
       p]
      [(struct proof:1 ())
       (proof:1->proof:0 p)]
      [(struct proof:2 ())
       (proof:1->proof:0 (proof:2->proof:1 p))]))
  
  (define (proof->proof:1 p)
    (match p
      [(struct proof:0 ())
       p]
      [(struct proof:1 ())
       p]
      [(struct proof:2 ())
       (proof:2->proof:1 p)]))
  
  (define proof-print-seen (make-parameter empty))
  
  (define (proof-print p)    
    (void (proof-print* 1 p)))
  
  (define (proof-print* i p)
    (match p
      [(struct proof:assume (a))
       (let/ec esc
         (for-each (match-lambda
                     [(list-rest ai (? (lambda (x) (equal? x a))))
                      (printf/indent "~a. Reiterate (~a): ~S~n" i ai a)
                      (esc (add1 i))]
                     [_
                      (void)])
                   (proof-print-seen))
         (printf/indent "~a. ASSUME ~S~n" i a)
         (add1 i))]
      [(struct proof:as:1 (a b))
       (printf/indent "~a. AS1: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:as:2 (a b))
       (printf/indent "~a. AS2: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:as:3 (a b))
       (printf/indent "~a. AS3: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:as:4 (a b c))
       (printf/indent "~a. AS4: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:mp (f s))
       (define fi (proof-print* i f))
       (define si (proof-print* fi s))
       (printf/indent "~a. MP (~a, ~a): ~S~n" si (sub1 fi) (sub1 si) (proof-result-wff p))
       (add1 si)]
      [(struct proof:1 ())
       (if ((proof-level) . < . 1)
           (proof-print* i (proof:1->proof:0 p))
           (proof:1-print* i p))]
      [(struct proof:2 ())
       (if ((proof-level) . < . 2)
           (proof-print* i (proof:2->proof:1 p))
           (proof:2-print* i p))]))
  
  (define proof-result-wff
    (match-lambda
      [(struct proof:assume (a))
       a]
      [(struct proof:as:1 (a b))
       `((neg ,a) -> (,a -> ,b))]
      [(struct proof:as:2 (a b))
       `(,b -> (,a -> ,b))]
      [(struct proof:as:3 (a b))
       `((,a -> ,b) -> (((neg ,a) -> ,b) -> ,b))]
      [(struct proof:as:4 (a b c))
       `((,a -> (,b -> ,c)) -> ((,a -> ,b) -> (,a -> ,c)))]
      [(struct proof:mp (f^ s^))
       (define f (proof-result-wff f^))
       (define s (proof-result-wff s^))
       (match s
         [`(,f -> ,c)
           c])]
      [(and p (struct proof:1 ()))
       (proof:1-result-wff p)]
      [(and p (struct proof:2 ()))
       (proof:2-result-wff p)]))
  
  (define (ASSUME a)
    (make-proof:assume a))
  (define (MP f^ s^)
    (define f (proof-result-wff f^))
    (define s (proof-result-wff s^))
    (match (list f s)
      [(list `,a `(,a -> ,b))
       (make-proof:mp f^ s^)]
      [_
       (error 'proofl "Error in instance of Modus Ponens, consequent does not follow:~n\tf: ~a\n\ts: ~a" f s)]))
  (define (AS1 a b)
    (make-proof:as:1 a b))
  (define (AS2 a b)
    (make-proof:as:2 a b))
  (define (AS3 a b)
    (make-proof:as:3 a b))
  (define (AS4 a b c)
    (make-proof:as:4 a b c))
  
  (provide/contract
   [wff? (any/c . -> . boolean?)]
   [proof? (any/c . -> . boolean?)]
   [proof-result-wff (proof? . -> . wff?)]
   [ASSUME (wff? . -> . proof?)]
   [MP (proof? proof? . -> . proof?)]
   [AS1 (wff? wff? . -> . proof?)]
   [AS2 (wff? wff? . -> . proof?)]
   [AS3 (wff? wff? . -> . proof?)]
   [AS4 (wff? wff? wff? . -> . proof?)])
  
  ;; Substitution
  (define (wff-subst wff a->b)
    (match wff
      [(? symbol?)
       (hash-table-get a->b wff (lambda () wff))]
      [`(neg ,a)
        `(neg ,(wff-subst a a->b))]
      [`(,a -> ,b)
        `(,(wff-subst a a->b) -> ,(wff-subst b a->b))]))
  
  (define (proof-subst p a->b)
    (match p
      [(struct proof:assume (a))
       (make-proof:assume (wff-subst a a->b))]
      [(struct proof:as:1 (a b))
       (make-proof:as:1 (wff-subst a a->b) (wff-subst b a->b))]
      [(struct proof:as:2 (a b))
       (make-proof:as:2 (wff-subst a a->b) (wff-subst b a->b))]
      [(struct proof:as:3 (a b))
       (make-proof:as:3 (wff-subst a a->b) (wff-subst b a->b))]
      [(struct proof:as:4 (a b c))
       (make-proof:as:4 (wff-subst a a->b) (wff-subst b a->b) (wff-subst c a->b))]
      [(struct proof:mp (f s))
       ; Runs the check again!
       (MP (proof-subst f a->b) (proof-subst s a->b))]))
  
  (provide/contract
   [wff-subst (wff? hash-table? . -> . wff?)]
   [proof-subst (proof? hash-table? . -> . proof?)])
  
  ;; Proof Level 1  
  (define-struct (proof:1 proof) ())
  (define-struct (proof:aa proof:1) (pa b))
  (define-struct (proof:r proof:1) (a))
  (define-struct (proof:cw proof:1) (a b c))
  (define-struct (proof:emp proof:1) (p0 p1))
  (define-struct (proof:p* proof:1) (a b c))
  (define-struct (proof:sa proof:1) (a b c))
  
  (define proof:1->proof:0
    (match-lambda
      [(struct proof:aa (pa b))
       (MP (proof:1->proof:0 pa) (AS2 b (proof-result-wff pa)))]
      [(struct proof:r (a))
       (MP (AS2 a a)
           (MP (AS2 `(,a -> ,a) a)
               (AS4 a `(,a -> ,a) a)))]
      [(struct proof:cw (a b c))
       (MP (MP (AS2 c b)
               (AS2 a `(,b -> (,c -> ,b))))
           (AS2 `(,a -> ,b) `(,a -> (,b -> (,c -> ,b)))))]
      [(struct proof:emp (p0 p1))
       (match (list (proof-result-wff p0) (proof-result-wff p1))
         [(list `(,a -> ,b) `(,a -> (,b -> ,c)))
          (MP (proof:1->proof:0 p0)
              (MP (proof:1->proof:0 p1)
                  (AS4 a b c)))]
         [(list w0 w1)
          (error 'proofl "Error in instance of Embedded Modus Ponens, consequent does not follow:\n\tf: ~a\n\ts: ~a" w0 w1)])]
      [(struct proof:p* (a b c))
       (EMP (AS2 c `(,a -> ,b))
            (AA (AS4 c a b)
                `(,a -> ,b)))]
      [(struct proof:sa (a b c))
       (EMP (AA (AS2 a b)
                `((,a -> ,b) -> ,c))
            (P* `(,a -> ,b) c b))]
      [(and p (struct proof ()))
       (proof->proof:0 p)]))
  
  (define proof:1-result-wff
    (match-lambda
      [(struct proof:aa (pa b))
       `(,b -> ,(proof-result-wff pa))]
      [(struct proof:r (a))
       `(,a -> ,a)]
      [(struct proof:cw (a b c))
       `((,a -> ,b) -> (,a -> (,b -> (,c -> ,b))))]
      [(struct proof:emp (p0 p1))
       (match (list (proof-result-wff p0) (proof-result-wff p1))
         [(list `(,a -> ,b) `(,a -> (,b -> ,c)))
          `(,a -> ,c)])]
      [(struct proof:p* (a b c))
       `((,a -> ,b) -> ((,c -> ,a) -> (,c -> ,b)))]
      [(struct proof:sa (a b c))
       `(((,a -> ,b) -> ,c) -> (,b -> ,c))]))
  
  (define (proof:1-print* i p)    
    (match p
      [(struct proof:aa (pa b))
       (define fi (proof-print* i pa))
       (printf/indent "~a. Adding an Antecedent (~a): ~S~n" fi (sub1 fi) (proof-result-wff p))
       (add1 fi)]
      [(struct proof:r (a))
       (printf/indent "~a. Reflexivity: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:cw (a b c))
       (printf/indent "~a. Weaking the Consequent: ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:emp (p0 p1))
       (define fi (proof-print* i p0))
       (define si (proof-print* fi p1))
       (printf/indent "~a. Embedded MP (~a, ~a): ~S~n" si (sub1 fi) (sub1 si) (proof-result-wff p))
       (add1 si)]
      [(struct proof:p* (a b c))
       (printf/indent "~a. Principle (*): ~S~n" i (proof-result-wff p))
       (add1 i)]
      [(struct proof:sa (a b c))
       (printf/indent "~a. Strengthening the Antecedent: ~S~n" i (proof-result-wff p))
       (add1 i)]))
  
  (define (AA a b)
    (make-proof:aa a b))  
  (define (R a)
    (make-proof:r a))
  (define (CW a b c)
    (make-proof:cw a b c))
  (define (EMP p0 p1)
    (make-proof:emp p0 p1))
  (define (P* a b c)
    (make-proof:p* a b c))
  (define (SA a b c)
    (make-proof:sa a b c))
  
  ;;; Examples
  ; (A -> B) -> (A -> A)
  (define (P1 a b)
    (MP (AS2 b a) (AS4 a b a)))
  ; A, (neg A) |- B
  (define (P2 a na b)
    (MP a (MP na (AS1 a b))))  
  
  ; |- (A -> B) -> ((neg B) -> (neg A))
  (define (CONTRA a b)
    ; |- A -> ((neg A) -> B)
    (define (P5-4a a b)
      (EMP (MP (AS2 a `(neg (neg ,a)))
               (MP (AS1 a `(neg (neg ,a)))
                   (AS3 `(neg ,a) `(,a -> (neg (neg ,a))))))
           (AA (AS1 `(neg ,a) b)
               a)))    
    ; Proof
    (EMP (AA (AS2 `(neg ,b) `(neg ,a)) 
             `(,a -> ,b))
         (EMP (MP (AA (P5-4a b `(neg ,a))
                      a)
                  (AS4 a b `((neg ,b) -> (neg ,a))))
              (AA (AS3 a `((neg ,b) -> (neg ,a)))
                  `(,a -> ,b)))))
  
  (provide/contract
   [AA (proof? wff? . -> . proof?)]
   [R (wff? . -> . proof?)]
   [CW (wff? wff? wff? . -> . proof?)]
   [EMP (proof? proof? . -> . proof?)]
   [P* (wff? wff? wff? . -> . proof?)]
   [SA (wff? wff? wff? . -> . proof?)]
   [CONTRA (wff? wff? . -> . proof?)])
  
  ;; Dededuction theorem
  (define-struct (proof:2 proof) ())
  (define-struct (proof:ded proof:2) (asmp pb))
  
  (define proof:2->proof:1
    (match-lambda
      [(struct proof:ded (asmp pb))
       (define p0 (ASSUME asmp))
       (define p1 pb)
       (match (proof->proof:0 p1)
         ; \delta = \alpha
         [(struct proof:assume ((? (lambda (a) (equal? a asmp)))))
          (R asmp)]
         ; \delta is an axiom
         [(struct proof:as:1 (a b))
          (AA (proof->proof:1 p1) asmp)]
         [(struct proof:as:2 (a b))
          (AA (proof->proof:1 p1) asmp)]
         [(struct proof:as:3 (a b))
          (AA (proof->proof:1 p1) asmp)]
         [(struct proof:as:4 (a b c))
          (AA (proof->proof:1 p1) asmp)]
         ; \delta in \gamma
         [(struct proof:assume (a))
          (AA (proof->proof:1 p1) asmp)]
         ; \delta came from \sigma and (\sigma -> \delta)
         [(struct proof:mp (s_p s->d_p))
          (EMP (proof:2->proof:1 (Ded asmp (lambda (pa) s_p)))
               (proof:2->proof:1 (Ded asmp (lambda (pa) s->d_p))))])]))
  
  (define proof:2-result-wff
    (match-lambda
      [(struct proof:ded (asmp pb))
       `(,asmp -> ,(proof-result-wff pb))]))
  
  (define (proof:2-print* i p)
    (match p
      [(struct proof:ded (a pb))
       (define fi
         (parameterize ([indent-level (add1 (indent-level))])
           (printf/indent "~a. Assume: ~S~n" i a)
           (parameterize ([proof-print-seen (list* (cons i a) (proof-print-seen))])
             (proof-print* (add1 i) pb))))
       (printf/indent "~a. Ded (~a-~a): ~S~n" fi i (sub1 fi) (proof-result-wff p))
       (add1 fi)]))
  
  (define (Ded asmp p-maker)
    (define p0 (ASSUME asmp))
    (define p1 (p-maker p0))
    (make-proof:ded asmp p1))
  
  (provide/contract
   [Ded (wff? (proof? . -> . proof?) . -> . proof?)])
  
  ; (neg A) -> A |- (A -> B) -> B
  (define (DP0 p b)
    (define a (match (proof-result-wff p) [`((neg ,a) -> ,a) a]))
    (define a_p
      (MP p
          (MP (R a)
              (AS3 a a))))
    (Ded `(,a -> ,b)
         (lambda (ep)
           (MP a_p ep))))
  ; |- (A -> (B -> C)) -> ((A -> B) -> (A -> C))
  (define (DP1 a b c)
    (Ded `(,a -> (,b -> ,c))
         (lambda (p1)
           (Ded `(,a -> ,b)
                (lambda (p2)
                  (EMP p2 p1))))))
  ; |- (A -> (B -> C)) -> ((A -> B) -> (A -> C))
  (define (DP2 a b c)
    (Ded `(,a -> (,b -> ,c))
         (lambda (p1)
           (Ded `(,a -> ,b)
                (lambda (p2)
                  (Ded a
                       (lambda (p3)
                         (MP (MP p3 p2)
                             (MP p3 p1)))))))))
  ; |- B -> (A -> B)
  (define (DP3 a b)
    (Ded b
         (lambda (p1)
           (Ded a
                (lambda (p2)
                  p1)))))
  ; A -> B |- B (Demonstrates that incorrect reiteration is not possible)
  (define (DP4 p1 a b)
    (Ded a
         (lambda (p2)
           (MP p2 p1))))
  
  ;; Negation Introduction
  (define (CONTRAP p)
    (match (proof-result-wff p)
      [`(,a -> ,b)
        (MP p
            (CONTRA a b))]))
  
  (define (DNI ap)
    (define a (proof-result-wff ap))
    (MP ap
        (Ded a
             (lambda (pa)
               (NI `(neg ,a)
                   (lambda (pna)
                     pa)
                   (lambda (pna)
                     pna))))))
  
  (define (DNE p)    
    (match (proof-result-wff p)
      [`(neg (neg ,a))
        (MP p
            ; XXX !
            (ASSUME `((neg (neg ,a)) -> ,a)))]))
  
  (define (NI a ->b ->nb)
    (define a->bp (Ded a ->b))
    (define b (match (proof-result-wff a->bp) [`(,a -> ,b) b]))
    (MP (CONTRAP (Ded a ->nb))
        (MP (CONTRAP a->bp)
            (AS3 `(neg ,b) `(neg ,a)))))
  
  (provide/contract
   [CONTRAP (proof? . -> . proof?)]
   [DNI (proof? . -> . proof?)]
   [DNE (proof? . -> . proof?)]
   [NI (wff? (proof? . -> . proof?) (proof? . -> . proof?) . -> . proof?)])
  
  ; a, (neg a) |- b
  (define (NI0 a b)
    (DNE (NI `(neg ,b) 
             (lambda (nbp) (ASSUME a))
             (lambda (nbp) (ASSUME `(neg ,a))))))    
  
  ;; Theorem Prover
  (define wff-symbols
    (match-lambda
      [(and x (? symbol?))
       (list x)]
      [`(neg ,a)
        (wff-symbols a)]
      [`(,a -> ,b)
        (append (wff-symbols a) (wff-symbols b))]))
  
  (define (add-theorem new olds)
    (define new* (apply append
                        (map (lambda (old)
                               (append (with-handlers ([exn:fail? (lambda _ empty)])
                                         (list (MP old new)))
                                       (with-handlers ([exn:fail? (lambda _ empty)])
                                         (list (MP new old)))))
                             olds)))
    (define next (list* new olds))
    (foldl (lambda (e a)
             (add-theorem e a))
           next
           new*))
  
  (define (prove* advice gamma thm)
    (define gamma-wffs (map proof-result-wff gamma))    
    #;(pretty-print `(prove* ,advice ,gamma-wffs ,thm))
    (match thm
      [(? (lambda _ (member thm gamma-wffs)))
       (let/ec esc
         (for-each (lambda (p w)
                     (when (equal? thm w)
                       (esc p)))
                   gamma
                   gamma-wffs))]
      [(? symbol?)
       (let-values ([(subthm advice*)
                     (match advice
                       [(list)
                        (printf "Need advice!~n")
                        (printf "\t~S |- ~S~n" gamma-wffs thm)
                        (values (read) empty)]
                       [(list-rest a as)
                        (values a as)])])
         (MP (prove* advice* gamma subthm)
             (prove* advice* gamma `(,subthm . -> . ,thm))))]
      [`(,a -> ,b)
        (Ded a
             (lambda (ap)
               (prove* advice (add-theorem ap gamma) b)))]
      [`(neg ,a)
        (let-values ([(b advice*)
                      (match advice
                        [(list)
                         (printf "Need advice!~n")
                         (printf "\t~S ; ~S |- ???~n" gamma-wffs a)
                         (printf "\t~S ; ~S |- (neg ???)~n" gamma-wffs a)
                         (values (read) empty)]
                        [(list-rest b bs)
                         (values b bs)])])
          (NI a 
              (lambda (ap)
                (prove* advice* (add-theorem ap gamma) b))
              (lambda (ap)
                (prove* advice* (add-theorem ap gamma) `(neg ,b)))))]))
  
  (define/kw (prove thm #:optional [advice empty])
    (prove* advice empty thm))
  
  (provide/contract
   [prove (((list/c proof?)) ((list/c wff?)) . opt-> . proof?)]
   [prove* ((list/c wff?) (list/c proof?) wff? . -> . proof?)])
  
  ;; Examples:
  #; (prove `((a -> b) -> ((neg b) -> (neg a))) (list 'b))
  
  ;; Extended wffs
  (define ewff?
    (match-lambda
      [`(,a OR ,b)
        (and (ewff? a) (ewff? b))]
      [`(,a AND ,b)
        (and (ewff? a) (ewff? b))]
      [`(,a IFF ,b)
        (and (ewff? a) (ewff? b))]
      [(? wff?)
       #t]))
  
  (define ewff->wff
    (match-lambda
      [`(,a OR ,b)
        `((neg ,(ewff->wff a)) -> ,(ewff->wff b))]
      [`(,a AND ,b)
        `(neg (,(ewff->wff a) -> (neg ,(ewff->wff b))))]
      [`(,a IFF ,b)
        (ewff->wff `((,a -> ,b) AND (,b -> ,a)))]
      [(and f (? wff?))
       f]))
  
  (provide/contract
   [ewff? (any/c . -> . boolean?)]
   [ewff->wff (ewff? . -> . wff?)]))