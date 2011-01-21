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


		; A functional substitution in a assoc list
(define (new-mmap mmap tag new-body)
  (cond
   ((null? mmap) '())
   ((eq? tag (caar mmap))	; replacement
    (cons (cons tag new-body) (cdr mmap)))
   (else (cons (car mmap) (new-mmap (cdr mmap) tag new-body)))))


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
(define (make-dispatcher message-map)
  (define (dispatcher selector . args)
    (cond
      ((eq? selector 'mmap) message-map)
      ((assq selector message-map) =>
        (lambda (handler-ass)
          (apply (cdr handler-ass) (cons dispatcher args))))
      ((eq? selector 'my-class) (list dispatcher "UNKNOWN")) ; if wasn't defined
      (else						     ; in message-map
        (error (dispatcher 'my-class) " does not understand " selector))))
  dispatcher)


		; point-2D object and its constructor

(define (make-point-2D x y)
  (define (my-identity) message-map)
  (define message-map
    `((get-x . ,(lambda (self) (list self x)))
      (get-y . ,(lambda (self) (list self y)))
      (set-x . ,(lambda (self new-x)
		  (list
		   (make-dispatcher
		    (new-mmap (self 'mmap) 'get-x
			      (lambda (self) (list self new-x)))))))

      (set-y . ,(lambda (self new-y)
		  (list
		   (make-dispatcher
		    (new-mmap (self 'mmap) 'get-y
			      (lambda (self) (list self new-y)))))))
      (identity . ,(lambda (self) (list self my-identity)))
      (my-class . ,(lambda (self) (list self "point-2D")))
      (of-class . ,(lambda (self) (self 'my-class))) ; an example of
			; sending a message to myself
      ))
  (make-dispatcher message-map))

(define (print-x-y obj)
  (define (rev-apply lst handler) (apply handler lst))
  (rev-apply (obj 'get-x)
	     (lambda (obj x)
	       (rev-apply (obj 'get-y)
			  (lambda (obj y)
			    (rev-apply (obj 'my-class)
				       (lambda (obj my-class)
					 (list my-class x y))))))))

(define p (make-point-2D 5 6))
(define p1 (make-point-2D 5 6))
(p1 'of-class) ; ==> (#<procedure p1> "point-2D")
(p 'get-x)     ; ==> (#<procedure p> 5)
(p1 'get-x)    ; ==> (#<procedure p1> 5)

(print-x-y p)  ; ==> ("point-2D" 5 6)
; p and p1 happen at this point to be in the same state
(equal? (print-x-y p) (print-x-y p1)) ; ==> #t

; but p and p1 are different, non-identical objects
(eq? (cadr (p 'identity)) (cadr (p1 'identity))) ; ==> #f

; pm is the object 'p' after the "mutation"
; Note that closures 'pm' and 'p' _share_ all the common state,
; including their identity
(define pm (car (p 'set-x 10)))
(print-x-y pm) ; ==> ("point-2D" 10 6)

; States differ, identities are the same
(equal? (print-x-y p) (print-x-y pm)) ; ==> #f
(eq? (cadr (p 'identity)) (cadr (pm 'identity))) ; ==> #t

; Illustrating inheritance and polymorphism
; A derived "object" inherits the message-map of its parent, and
; adds its own handlers at the top. Because subclass' handlers will
; be encountered first when a handler for a selector is being
; searched, the subclass is able to override the behavior of its
; superclass.

(define (make-point-3D x y z)
  (define message-map
    (append
     `((get-z . ,(lambda (self) (list self z)))
       (set-z . ,(lambda (self new-z)
		   (list
		    (make-dispatcher
		     (new-mmap (self 'mmap) 'get-z
			      (lambda (self) (list self new-z)))))))
       (my-class . ,(lambda (self) (list self "point-3D")))
      )
     ((make-point-2D x y) 'mmap)))	; the superclass

   (make-dispatcher message-map))


(define q (make-point-3D 1 2 3))

; Although print-x-y was defined for objects of type point-2D,
; it accepts point-3D objects as well. Note however that the head
; of print-x-y's result spells "point-3D". This is because a point-3D
; object overrides the message 'my-class of its parent class
(print-x-y q)  ; ==> ("point-3D" 1 2)
(q 'get-z)     ; ==> (#<procedure q> 3)

; Demonstrating the use of inherited methods....
(let ((obj (car ((car (q 'set-x 11)) 'set-z 12))))
  (append (print-x-y obj) (cdr (obj 'get-z))))
; ==> ("point-3D" 11 2 12) 

(q 'of-class)
; ==> (#<procedure q> "point-3D") ; notice polymorphism!!!
; The of-class method is implemented in point-2D yet the result is
; "point-3D". This is because the 'of-class method sends the message
; 'my-class to itself. The latter handler is over-ridden in a
; class point-3D to return its own title, "point-3D".

