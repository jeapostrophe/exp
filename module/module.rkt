(module module '#%kernel
  (#%require racket/private/more-scheme
             racket/private/modbeg
             (for-syntax '#%kernel
                         racket/private/stxcase-scheme
                         racket/private/more-scheme
                         racket/private/letstx-scheme
                         racket/private/qqstx))

  (#%provide module+
             define-module+
             define-module*+)

  (begin-for-syntax
    (define-values (expect-identifier-for)
      (lambda (whole-stx stx where can-be-false?)
        (define-values (v) (syntax-e stx))
        (unless (or (and can-be-false? (not v))
                    (symbol? v))
          (raise-syntax-error #f
                              (format
                               "expected an identifier for ~a, found something else"
                               where)
                              whole-stx
                              stx))))

    (define-values (do-define-module+)
      (lambda (this which-module stx)
        (case (syntax-local-context)
          [(module-begin)
           (quasisyntax/loc stx (begin #,stx))]
          [(module)
           (syntax-case stx ()
             [(_ the-module+ the-submodule the-module-lang)
              (begin
                (expect-identifier-for stx #'the-module+ "the module+ form" #f)
                (expect-identifier-for stx #'the-submodule "a submodule" #f)
                (expect-identifier-for stx #'the-module-lang "the module language" #t)
                (quasisyntax/loc stx
                  (define-syntaxes (the-module+)
                    (lambda (module+-stx)
                      (do-module+-for #'#,which-module
                                      #'the-submodule
                                      (syntax-local-introduce #'the-module-lang)
                                      (syntax-local-introduce #'the-module-lang)
                                      module+-stx)))))])])))

    (define-values (do-module+-for)
      (lambda (which-module-stx the-submodule-stx the-module-lang-stx context-stx stx)
        (case (syntax-local-context)
          [(module-begin)
           (quasisyntax/loc stx (begin #,stx))]
          [(module)
           (syntax-case stx ()
             [(_ #:declared)
              (quasisyntax/loc stx
                (define-module
                  #,which-module-stx
                  #,the-submodule-stx
                  #,the-module-lang-stx))]
             [(_ e ...)
              (begin
                (when (hash-has-key? submodule->defined? (syntax-e the-submodule-stx))
                  (raise-syntax-error #f "submodule is already declared" stx))
                ;; This looks it up the first time and is allowed to create a
                ;; list and lift a module-end declaration if necessary:
                (let ([stxs-box (get-stxs-box which-module-stx
                                              context-stx
                                              the-submodule-stx
                                              the-module-lang-stx
                                              #t)])
                  (set-box!
                   stxs-box
                   (append (reverse (syntax->list (syntax-local-introduce #'(e ...))))
                           (unbox stxs-box))))
                (syntax/loc stx (begin)))])]
          [else
           (raise-syntax-error #f
                               "allowed only in a module body"
                               stx)]))))

  (define-syntaxes (define-module+)
    (lambda (stx)
      (do-define-module+ 'define-module+ #'module stx)))

  (define-syntaxes (define-module*+)
    (lambda (stx)
      (do-define-module+ 'define-module*+ #'module* stx)))

  (define-syntaxes (module+)
    (lambda (stx)
      (syntax-case stx ()
        [(_ the-submodule e ...)
         (begin
           (expect-identifier-for stx #'the-submodule "a submodule" #f)
           (do-module+-for #'module* #'the-submodule #'#f
                           stx
                           #'(fake-the-submodule+ e ...)))])))

  (begin-for-syntax
    ;; The following table is newly instantiated for each module
    ;; expansion that uses `module+', so it is effectively
    ;; module-local:
    (define-values (submodule->stxs-box) (make-weak-hash))
    (define-values (get-stxs-box)
      (lambda (which-module-stx form-stx the-submodule-stx the-module-lang-stx lift?)
        (hash-ref! submodule->stxs-box (syntax-e the-submodule-stx)
                   (lambda ()
                     (when lift?
                       (syntax-local-lift-module-end-declaration
                        ;; Use the lexical context of the first `module+'
                        ;; form as the context of the implicit `#%module-begin':
                        (datum->syntax
                         form-stx
                         (list #'define-module
                               which-module-stx
                               the-submodule-stx
                               the-module-lang-stx)
                         form-stx)))
                     (box null)))))

    (define-values (submodule->defined?) (make-weak-hash))
    (define-values (defined-or-define!)
      (lambda (the-submodule-stx)
        (let-values ([(k) (syntax-e the-submodule-stx)])
          (begin0 (hash-ref submodule->defined? k #t)
            (hash-ref! submodule->defined? k #f))))))

  ;; A use of this form is lifted to the end of the enclosing module
  ;; for each submodule created by `module+':
  (define-syntaxes (define-module)
    (lambda (stx)
      (syntax-case stx ()
        [(_ which-module the-submodule the-module-lang)
         (cond
           [(defined-or-define! #'the-submodule)
            (let ([stxs-box (get-stxs-box #f #f #'the-submodule #f #f)])
              ;; Propagate the lexical context of the first `module+'
              ;; for the implicit `#%module-begin':
              (datum->syntax
               stx
               (list*
                #'which-module
                #'the-submodule
                #'the-module-lang
                (map syntax-local-introduce (reverse (unbox stxs-box))))
               stx))]
           [else
            (syntax/loc stx (begin))])]))))
