#lang scheme

(define-syntax-rule (bind x e ...)
    (let ([x (random)]
          [z 10])
      (printf "~a~n" z)
      e ...))

(bind z z)

(define-syntax evil-searcher
  (syntax-rules (z)
    [(_ z ee (cont var . ec) fk)
     (cont ee . ec)]
    [(_ (zl . zr) (el . er) (cont var . ec) fk)
     (evil-searcher 
      zl el (cont var . ec)
      (evil-searcher zr er 
                     (cont var . ec)
                     fk))]
    [(_ _ _ (cont var . ec) fk)
     fk]))

(define-syntax evil-binder
  (syntax-rules ()
    [(_ binding val e ...)
     (let ([binding val])
       e ...)]))

(define-syntax bind-z
  (syntax-rules ()
    [(_ e ...)
     (evil-searcher 
      (e ...) (e ...)
      (evil-binder _ (random) e ...)
      (evil-binder q (random) e ...))]))

"Z"

(bind-z z)

(let ([z 10]) (bind-z (+ 10 z)))

(bind-z (+ 10 z))

(define-syntax (bind-z* stx)
  (syntax-case stx ()
    [(_ e)
     (with-syntax ([z (datum->syntax stx 'z)])
       (syntax/loc stx
         (let ([z (random)])
           e)))]))

"Z*"

(bind-z* z)

(let ([z 10]) (bind-z* (+ 10 z)))

(bind-z* (+ 10 z))
  
  