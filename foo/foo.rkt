#lang racket/base
; 	Purely-functional Object-Oriented System in Scheme
;
; The present code implements a classless, delegation-based OO system, similar
; to those of Self or Javascript. This is a full-fledged OO system with
; encapsulation, object identity, inheritance and polymorphism. It is also
; a purely functional system: there is not a single assignment or
; other mutation in the code below.
;
; A closure (encapsulating a message map, and private parameters if any)
; is the object in this system. Sending a message to an object -- i.e.,
; applying the object to a message selector and arguments, -- results
; in a list. Its head is the object in a new state, having processed the
; message; the rest of the list are the results of the message if any.
; Objects' identity is decided by an eq? predicate applied to the result of
; an 'identity' message. A "set-x" method returns an object with a new state,
; but with the same identity as the source object. An object in a changed
; state is in a sense a "child" of the original object. No wonder
; implementations of "mutation" and inheritance are so similar in this
; OO system.
;
; This code was meant to be "light"; therefore it deliberately uses only the
; most basic Scheme constructions. No macros/syntactic closures are employed
; (although they are certainly possible and appropriate).
;
; This code has been discussed in an article "Re: FP, OO and relations. Does
; anyone trump the others?"
; posted on comp.lang.smalltalk, comp.lang.functional, and comp.lang.scheme
; on Wed Dec 29 05:13:58 1999 GMT, Message-ID: <84c4qe$48j$1@nnrp1.deja.com>
; See also http://pobox.com/~oleg/ftp/Scheme/oop-in-fp.txt
; The article presents a more familiar OO system with mutations, and contrasts
; it with a purely-functional OO system, which is implemented in this present
; file.
;
; $Id: pure-oo-system.scm,v 1.2 2000/03/01 02:50:40 oleg Exp oleg $
(require (for-syntax racket/base
                     syntax/parse
                     "foo-stx.rkt")
         racket/stxparam)

(define-syntax (define-method stx)
  (syntax-parse
   stx
   [(_ m:id)
    (syntax/loc stx
      (begin
        (define m-id (gensym 'm))
        (define-syntax m (method #'m-id))))]))
(define-syntax-rule (define-method* m ...)
  (begin (define-method m) ...))

(define-syntax-parameter self 
  (λ (stx) (raise-syntax-error 'self "Used outside mmap")))
(define mmap-empty (hasheq))
(define mmap-set hash-set)
(define mmap-ref hash-ref)
(define-syntax (mmap stx)
  (syntax-parse
   stx
   #:literals (define)
   [(_ parent-e:expr)
    (syntax/loc stx parent-e)]
   [(_ parent-e:expr
       (define ((~var message (static method? "method")) . fmls) body:expr ...)
       n ...)
    (with-syntax ([m-id (method-id (attribute message.value))])
      (syntax/loc stx
        (mmap (mmap-set parent-e
                        m-id
                        ; XXX Keywords
                        (λ (the-self . fmls)
                          (syntax-parameterize ([self (make-rename-transformer #'the-self)])
                                               body ...)))
              n ...)))]))

; This function makes a new dispatcher closure -- a new
; object: a dispatcher _is_ an object.
; A message map is a list of associations of message
; selectors with message handlers. A message selector
; is a symbol. A message handler is a procedure. It should
; take the dispatcher (i.e., _self_) as the first argument,
; and message's arguments as other parameters, if any.
; Every object always accepts a message 'mmap and replies with
; its message map. This feature is used to create an
; object with a new state, and to implement a delegation-based
; inheritance (see make-point-3D below). The similarity
; between the two runs deeper: an object with a changed state
; is in a sense a "child" of the original object.
(struct an-object (mmap)
        #:property prop:procedure
        ; XXX keywords
        (λ (ao sel . args)
          (define message-map (an-object-mmap ao))
          ; XXX keywords
          (apply (mmap-ref message-map sel 
                           (λ () (error 'object "~a does not understand ~v"
                                        (my-class ao) sel)))
                 ao args)))

(define-syntax (object stx)
  (syntax-parse
   stx
   ; XXX parent contract
   [(_ parent:expr m ...)
    (syntax/loc stx
      (an-object
       (mmap (an-object-mmap parent)
             m ...)))]))

(define-method* identity my-class)
(define (object%)
  (define me (gensym 'obj))
  (an-object
   (mmap mmap-empty
         (define (my-class) "object")
         (define (identity) me))))

;;;;;;; Tests
(require tests/eli-tester)

; point-2D object and its constructor

(define-method* get-x get-y set-x set-y of-class)
(define (make-point-2D x y)
  (object (object%)
          (define (get-x) x)
          (define (get-y) y)
          (define (set-x new-x)
            (object self 
                    (define (get-x) new-x)))
          (define (set-y new-y)
            (object self
                    (define (get-y) new-y)))
          (define (my-class)
            "point-2D")
          (define (of-class)
            (my-class self))))

(define (print-x-y obj)
  (list (my-class obj)
        (get-x obj)
        (get-y obj)))

(define p (make-point-2D 5 6))
(define p1 (make-point-2D 5 6))
(test
 (of-class p1) => "point-2D"
 (get-x p) => 5
 (get-x p1) => 5
 
 (print-x-y p) => (list "point-2D" 5 6)
 ; p and p1 happen at this point to be in the same state
 (equal? (print-x-y p) (print-x-y p1))
 
 ; but p and p1 are different, non-identical objects
 (eq? (identity p) (identity p1)) => #f)

; pm is the object 'p' after the "mutation"
; Note that closures 'pm' and 'p' _share_ all the common state,
; including their identity
(define pm (set-x p 10))
(test
 (print-x-y pm) => (list "point-2D" 10 6)
 
 ; States differ, identities are the same
 (equal? (print-x-y p) (print-x-y pm)) => #f
 (eq? (identity p) (identity pm)))

; Illustrating inheritance and polymorphism
; A derived "object" inherits the message-map of its parent, and
; adds its own handlers at the top. Because subclass' handlers will
; be encountered first when a handler for a selector is being
; searched, the subclass is able to override the behavior of its
; superclass.

(define-method* get-z set-z)
(define (make-point-3D x y z)
  (object (make-point-2D x y)
          (define (get-z) z)
          (define (set-z new-z)
            (object self
                    (define (get-z) new-z)))
          (define (my-class)
            "point-3D")))

(define q (make-point-3D 1 2 3))

(test
 ; Although print-x-y was defined for objects of type point-2D,
 ; it accepts point-3D objects as well. Note however that the head
 ; of print-x-y's result spells "point-3D". This is because a point-3D
 ; object overrides the message 'my-class of its parent class
 (print-x-y q) => (list "point-3D" 1 2)
 (get-z q) => 3
 
 ; Demonstrating the use of inherited methods....
 (let ([obj (set-z (set-x q 11) 12)])
   (append (print-x-y obj) (list (get-z obj))))
 => (list "point-3D" 11 2 12) 
 
 (of-class q) => "point-3D" ; notice polymorphism!!!
 ; The of-class method is implemented in point-2D yet the result is
 ; "point-3D". This is because the 'of-class method sends the message
 ; 'my-class to itself. The latter handler is over-ridden in a
 ; class point-3D to return its own title, "point-3D".
 
 )