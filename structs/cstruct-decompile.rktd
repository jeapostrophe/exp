(begin
  (quote inspector insp0)
  (module cstruct ....
    (quote self #0={#%modidx #f #f})
    (quote
     internal-context
     (#%decode-syntax
      {wrap
       #({wrap
          #t
          #1=#hasheq()
          #s((wrap zo 0)
             ()
             #2=(#s((scope #(2 3 4) zo 0) 4 module () () #f))
             ((#3=#s((multi-scope #(2) zo 0)
                     4
                     cstruct
                     ((0
                       #4=#s((scope #(2 3 4) zo 0)
                             5
                             module
                             ((N
                               #5=(#4# . #2#)
                               #6=#s((module-binding binding 0 zo 0)
                                     (insp0 . #0#)))
                              (_cs #5# #6#)
                              (_cs-pointer #5# #6#)
                              (_cs-pointer/null #5# #6#)
                              (cs #5# #6#)
                              (cs->list #5# #6#)
                              (cs->list* #5# #6#)
                              (cs-tag #5# #6#)
                              (cs-x #5# #6#)
                              (cs-x-type #5# #6#)
                              (cs-y #5# #6#)
                              (cs-y-type #5# #6#)
                              (cs? #5# #6#)
                              (list*->cs #5# #6#)
                              (list->cs #5# #6#)
                              (make-cs #5# #6#)
                              (set-cs-x! #5# #6#)
                              (set-cs-y! #5# #6#)
                              (test-check-fun #5# #6#)
                              (test-fun #5# #6#)
                              (test-unsafe-fun #5# #6#)
                              (unsafe-cs-x #5# #6#)
                              (unsafe-cs-y #5# #6#)
                              (wrap-cs-type #5# #6#))
                             ((#5#
                               #s((all-from-module zo 0)
                                  #7={#%modidx racket/base #f}
                                  0
                                  0
                                  insp0
                                  ()
                                  #f))
                              (#5#
                               #s((all-from-module zo 0)
                                  {#%modidx racket/flonum #f}
                                  0
                                  0
                                  insp0
                                  ()
                                  #f))
                              (#5#
                               #s((all-from-module zo 0)
                                  #8={#%modidx ffi/unsafe #f}
                                  0
                                  0
                                  insp0
                                  ()
                                  #f))
                              (#5#
                               #s((all-from-module zo 0)
                                  #9={#%modidx racket/unsafe/ops #f}
                                  0
                                  0
                                  insp0
                                  ()
                                  #f)))
                             #3#))
                      (1
                       #10=#s((scope #(2 3 4) zo 0)
                              6
                              module
                              ()
                              (((#10# . #2#)
                                #s((all-from-module zo 0)
                                   #7#
                                   1
                                   0
                                   insp0
                                   ()
                                   #f)))
                              #3#))))
               0)))}
         {wrap #f #1# #s((wrap zo 0) () () ((#3# 0)))})
       #1#
       #s((wrap zo 0) () () ())}))
    (quote
     bindings
     #hasheq((0
              .
              #hasheq((unsafe-cs-y
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-y
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           31
                           10
                           621
                           11)
                         #1#
                         #11=#s((wrap zo 0)
                                (#s((module-shift zo 0)
                                    {#%modidx #f #f}
                                    #0#
                                    #f
                                    #f))
                                #2#
                                ((#3# 0)))}))
                      (x-offset5.0
                       .
                       (#%decode-syntax
                        {wrap
                         x-offset5
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#12=#s((scope #(2 3 4) zo 0)
                                    12
                                    macro
                                    ((x-offset5
                                      (#12#
                                       .
                                       #13=(#14=#s((scope #(2 3 4) zo 0)
                                                   7
                                                   macro
                                                   ((^TYPE-tag
                                                     #15=(#14#
                                                          #4#
                                                          #16=#s((scope
                                                                  #(2 3 4)
                                                                  zo
                                                                  0)
                                                                 1
                                                                 module
                                                                 ((*in-array
                                                                   #17=(#16#
                                                                        .
                                                                        #18=(#s((scope
                                                                                 #(2
                                                                                   3
                                                                                   4)
                                                                                 zo
                                                                                 0)
                                                                                0
                                                                                module
                                                                                ()
                                                                                ()
                                                                                #f)))
                                                                   #19=#s((module-binding
                                                                           binding
                                                                           0
                                                                           zo
                                                                           0)
                                                                          (insp0
                                                                           .
                                                                           #20={#%modidx
                                                                                #f
                                                                                #f})))
                                                                  (->
                                                                   #17#
                                                                   #19#)
                                                                  (:array-gen
                                                                   #17#
                                                                   #19#)
                                                                  (_?
                                                                   #17#
                                                                   #19#)
                                                                  (_array
                                                                   #17#
                                                                   #19#)
                                                                  (_array/list
                                                                   #17#
                                                                   #19#)
                                                                  (_array/vector
                                                                   #17#
                                                                   #19#)
                                                                  (_bitmask
                                                                   #17#
                                                                   #19#)
                                                                  (_bitmask*
                                                                   #17#
                                                                   #19#)
                                                                  (_box
                                                                   #17#
                                                                   #19#)
                                                                  (_byte
                                                                   #17#
                                                                   #19#)
                                                                  (_bytes*
                                                                   #17#
                                                                   #19#)
                                                                  (_bytes/eof
                                                                   #17#
                                                                   #19#)
                                                                  (_cpointer
                                                                   #17#
                                                                   #19#)
                                                                  (_cpointer/null
                                                                   #17#
                                                                   #19#)
                                                                  (_cprocedure
                                                                   #17#
                                                                   #19#)
                                                                  (_cprocedure*
                                                                   #17#
                                                                   #19#)
                                                                  (_enum
                                                                   #17#
                                                                   #19#)
                                                                  (_enum*
                                                                   #17#
                                                                   #19#)
                                                                  (_file
                                                                   #17#
                                                                   #19#)
                                                                  (_fun
                                                                   #17#
                                                                   #19#)
                                                                  (_gcable
                                                                   #17#
                                                                   #19#)
                                                                  (_int
                                                                   #17#
                                                                   #19#)
                                                                  (_intmax
                                                                   #17#
                                                                   #19#)
                                                                  (_intptr
                                                                   #17#
                                                                   #19#)
                                                                  (_list
                                                                   #17#
                                                                   #19#)
                                                                  (_list-struct
                                                                   #17#
                                                                   #19#)
                                                                  (_llong
                                                                   #17#
                                                                   #19#)
                                                                  (_long
                                                                   #17#
                                                                   #19#)
                                                                  (_or-null
                                                                   #17#
                                                                   #19#)
                                                                  (_ptr
                                                                   #17#
                                                                   #19#)
                                                                  (_ptrdiff
                                                                   #17#
                                                                   #19#)
                                                                  (_sbyte
                                                                   #17#
                                                                   #19#)
                                                                  (_short
                                                                   #17#
                                                                   #19#)
                                                                  (_sint
                                                                   #17#
                                                                   #19#)
                                                                  (_sint16
                                                                   #17#
                                                                   #19#)
                                                                  (_sint32
                                                                   #17#
                                                                   #19#)
                                                                  (_sint64
                                                                   #17#
                                                                   #19#)
                                                                  (_sint8
                                                                   #17#
                                                                   #19#)
                                                                  (_sintptr
                                                                   #17#
                                                                   #19#)
                                                                  (_size
                                                                   #17#
                                                                   #19#)
                                                                  (_sllong
                                                                   #17#
                                                                   #19#)
                                                                  (_slong
                                                                   #17#
                                                                   #19#)
                                                                  (_sshort
                                                                   #17#
                                                                   #19#)
                                                                  (_ssize
                                                                   #17#
                                                                   #19#)
                                                                  (_string
                                                                   #17#
                                                                   #19#)
                                                                  (_string*/latin-1
                                                                   #17#
                                                                   #19#)
                                                                  (_string*/locale
                                                                   #17#
                                                                   #19#)
                                                                  (_string*/utf-8
                                                                   #17#
                                                                   #19#)
                                                                  (_string/eof
                                                                   #17#
                                                                   #19#)
                                                                  (_string/latin-1
                                                                   #17#
                                                                   #19#)
                                                                  (_string/locale
                                                                   #17#
                                                                   #19#)
                                                                  (_string/utf-8
                                                                   #17#
                                                                   #19#)
                                                                  (_sword
                                                                   #17#
                                                                   #19#)
                                                                  (_ubyte
                                                                   #17#
                                                                   #19#)
                                                                  (_uint
                                                                   #17#
                                                                   #19#)
                                                                  (_uintmax
                                                                   #17#
                                                                   #19#)
                                                                  (_uintptr
                                                                   #17#
                                                                   #19#)
                                                                  (_ullong
                                                                   #17#
                                                                   #19#)
                                                                  (_ulong
                                                                   #17#
                                                                   #19#)
                                                                  (_union
                                                                   #17#
                                                                   #19#)
                                                                  (_ushort
                                                                   #17#
                                                                   #19#)
                                                                  (_uword
                                                                   #17#
                                                                   #19#)
                                                                  (_vector
                                                                   #17#
                                                                   #19#)
                                                                  (_word
                                                                   #17#
                                                                   #19#)
                                                                  (add-equality-property
                                                                   #17#
                                                                   #19#)
                                                                  (any-string-op
                                                                   #17#
                                                                   #19#)
                                                                  (array
                                                                   #17#
                                                                   #19#)
                                                                  (array-length
                                                                   #17#
                                                                   #19#)
                                                                  (array-ptr
                                                                   #17#
                                                                   #19#)
                                                                  (array-ref
                                                                   #17#
                                                                   #19#)
                                                                  (array-set!
                                                                   #17#
                                                                   #19#)
                                                                  (array-type
                                                                   #17#
                                                                   #19#)
                                                                  (array?
                                                                   #17#
                                                                   #19#)
                                                                  (cast
                                                                   #17#
                                                                   #19#)
                                                                  (cblock->list
                                                                   #17#
                                                                   #19#)
                                                                  (cblock->vector
                                                                   #17#
                                                                   #19#)
                                                                  (check-is-property
                                                                   #17#
                                                                   #19#)
                                                                  (compute-offsets
                                                                   #17#
                                                                   #19#)
                                                                  (cpointer-has-tag?
                                                                   #17#
                                                                   #19#)
                                                                  (cpointer-maker
                                                                   #17#
                                                                   #19#)
                                                                  (cpointer-push-tag!
                                                                   #17#
                                                                   #19#)
                                                                  (cstruct-info
                                                                   #17#
                                                                   #19#)
                                                                  (ctype->layout
                                                                   #17#
                                                                   #19#)
                                                                  (ctype-coretype
                                                                   #17#
                                                                   #19#)
                                                                  (default-_string-type
                                                                   #17#
                                                                   #19#)
                                                                  (define*
                                                                   #17#
                                                                   #19#)
                                                                  (define-c
                                                                   #17#
                                                                   #19#)
                                                                  (define-cpointer-type
                                                                   #17#
                                                                   #19#)
                                                                  (define-cstruct
                                                                   #17#
                                                                   #19#)
                                                                  (define-fun-syntax
                                                                   #17#
                                                                   #19#)
                                                                  (false-or-op
                                                                   #17#
                                                                   #19#)
                                                                  (ffi-get
                                                                   #17#
                                                                   #19#)
                                                                  (ffi-obj-ref
                                                                   #17#
                                                                   #19#)
                                                                  (ffi-objects-ref-table
                                                                   #17#
                                                                   #19#)
                                                                  (ffi-set!
                                                                   #17#
                                                                   #19#)
                                                                  (function-ptr
                                                                   #17#
                                                                   #19#)
                                                                  (get-ffi-lib
                                                                   #17#
                                                                   #19#)
                                                                  (get-ffi-lib-internal
                                                                   #17#
                                                                   #19#)
                                                                  (get-ffi-obj
                                                                   #17#
                                                                   #19#)
                                                                  (get-ffi-obj*
                                                                   #17#
                                                                   #19#)
                                                                  (get-ffi-obj-name
                                                                   #17#
                                                                   #19#)
                                                                  (get-lowlevel-object
                                                                   #17#
                                                                   #19#)
                                                                  (held-callbacks
                                                                   #17#
                                                                   #19#)
                                                                  (in-array
                                                                   #17#
                                                                   #19#)
                                                                  (killer-thread
                                                                   #17#
                                                                   #19#)
                                                                  (lib-suffix
                                                                   #17#
                                                                   #19#)
                                                                  (lib-suffix-re
                                                                   #17#
                                                                   #19#)
                                                                  (list->cblock
                                                                   #17#
                                                                   #19#)
                                                                  (make-array
                                                                   #17#
                                                                   #19#)
                                                                  (make-c-parameter
                                                                   #17#
                                                                   #19#)
                                                                  (make-union
                                                                   #17#
                                                                   #19#)
                                                                  (prim-synonyms
                                                                   #17#
                                                                   #19#)
                                                                  (register-finalizer
                                                                   #17#
                                                                   #19#)
                                                                  (set-ffi-obj!
                                                                   #17#
                                                                   #19#)
                                                                  (sizeof->3ints
                                                                   #17#
                                                                   #19#)
                                                                  (string-type->string/eof-type
                                                                   #17#
                                                                   #19#)
                                                                  (struct:array
                                                                   #17#
                                                                   #19#)
                                                                  (struct:union
                                                                   #17#
                                                                   #19#)
                                                                  (suffix-before-version?
                                                                   #17#
                                                                   #19#)
                                                                  (union
                                                                   #17#
                                                                   #19#)
                                                                  (union-ptr
                                                                   #17#
                                                                   #19#)
                                                                  (union-ref
                                                                   #17#
                                                                   #19#)
                                                                  (union-set!
                                                                   #17#
                                                                   #19#)
                                                                  (union-types
                                                                   #17#
                                                                   #19#)
                                                                  (union?
                                                                   #17#
                                                                   #19#)
                                                                  (vector->cblock
                                                                   #17#
                                                                   #19#)
                                                                  (version-sep
                                                                   #17#
                                                                   #19#))
                                                                 ((#17#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #7#
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#17#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      {#%modidx
                                                                       '#%foreign
                                                                       #f}
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#17#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      {#%modidx
                                                                       setup/dirs
                                                                       #f}
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#17#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #9#
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#17#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #21={#%modidx
                                                                           racket/private/for
                                                                           #f}
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f)))
                                                                 #22=#s((multi-scope
                                                                         #(2)
                                                                         zo
                                                                         0)
                                                                        69
                                                                        unsafe
                                                                        ((0
                                                                          #16#)
                                                                         (1
                                                                          #23=#s((scope
                                                                                  #(2
                                                                                    3
                                                                                    4)
                                                                                  zo
                                                                                  0)
                                                                                 2
                                                                                 module
                                                                                 ((_fun-keywords
                                                                                   #24=(#23#
                                                                                        .
                                                                                        #18#)
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       _fun-keywords
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       _fun-keywords)))
                                                                                  (custom-type->keys
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       custom-type->keys
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       custom-type->keys)))
                                                                                  (disarm
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       disarm
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       disarm)))
                                                                                  (expand-fun-syntax/fun
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       expand-fun-syntax/fun
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       expand-fun-syntax/fun)))
                                                                                  (expand-fun-syntax/normal
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       expand-fun-syntax/normal
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       expand-fun-syntax/normal)))
                                                                                  (fun-syntax-name
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       fun-syntax-name
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax-name)))
                                                                                  (fun-syntax-proc
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       fun-syntax-proc
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax-proc)))
                                                                                  (fun-syntax?
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       fun-syntax?
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax?)))
                                                                                  (id=?
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       id=?
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       id=?)))
                                                                                  (make-fun-syntax
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       make-fun-syntax
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       make-fun-syntax)))
                                                                                  (orig-inspector
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       orig-inspector
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       orig-inspector)))
                                                                                  (split-by
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       split-by
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       split-by)))
                                                                                  (with-renamer
                                                                                   #24#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #20#
                                                                                       1
                                                                                       with-renamer
                                                                                       (#20#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       with-renamer))))
                                                                                 ((#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      1
                                                                                      0
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #21#
                                                                                      1
                                                                                      0
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      {#%modidx
                                                                                       racket/list
                                                                                       #f}
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      {#%modidx
                                                                                       syntax/stx
                                                                                       #f}
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#24#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      {#%modidx
                                                                                       racket/struct-info
                                                                                       #f}
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f)))
                                                                                 #22#))
                                                                         (2
                                                                          #25=#s((scope
                                                                                  #(2
                                                                                    3
                                                                                    4)
                                                                                  zo
                                                                                  0)
                                                                                 3
                                                                                 module
                                                                                 ()
                                                                                 (((#25#
                                                                                    .
                                                                                    #18#)
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      1
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f)))
                                                                                 #22#)))))
                                                          .
                                                          #18#)
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         ^TYPE-tag.0)))
                                                    (^TYPE?
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         ^TYPE?.0)))
                                                    (_^TYPE
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         _^TYPE.0)))
                                                    (_^TYPE/null
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         _^TYPE/null.0)))
                                                    (alignment-v
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         alignment-v.0)))
                                                    (all-offsets
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         all-offsets.0)))
                                                    (all-tags
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         all-tags.0)))
                                                    (all-types
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         all-types.0)))
                                                    (list*->super
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         list*->super.0)))
                                                    (offsets
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         offsets.0)))
                                                    (struct:cpointer:super
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         struct:cpointer:super.0)))
                                                    (super->list*
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super->list*.0)))
                                                    (super-offsets
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super-offsets.0)))
                                                    (super-pointer
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super-pointer.0)))
                                                    (super-tags
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super-tags.0)))
                                                    (super-types
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super-types.0)))
                                                    (super-wrap-type-type
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         super-wrap-type-type.0)))
                                                    (types
                                                     #15#
                                                     #s((module-binding
                                                         binding
                                                         0
                                                         zo
                                                         0)
                                                        (insp0
                                                         #0#
                                                         .
                                                         types.0))))
                                                   ()
                                                   #f)
                                            #4#))
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . x-offset5.0))))
                                    ()
                                    #f)
                             .
                             #26=(#14#))
                            ((#3# 0)))}))
                      (y-offset6.0
                       .
                       (#%decode-syntax
                        {wrap
                         y-offset6
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#27=#s((scope #(2 3 4) zo 0)
                                    13
                                    macro
                                    ((y-offset6
                                      (#27# . #13#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . y-offset6.0))))
                                    ()
                                    #f)
                             .
                             #26#)
                            ((#3# 0)))}))
                      (cs
                       .
                       (#%decode-syntax
                        {wrap
                         cs
                         #28=#(struct:srcloc
                               #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                               6
                               17
                               107
                               3)
                         #1#
                         #11#}))
                      (cs->list
                       .
                       (#%decode-syntax {wrap cs->list #28# #1# #11#}))
                      (wrap-cs-type
                       .
                       (#%decode-syntax {wrap wrap-cs-type #28# #1# #11#}))
                      (cs->list*
                       .
                       (#%decode-syntax {wrap cs->list* #28# #1# #11#}))
                      (cs-tag . (#%decode-syntax {wrap cs-tag #28# #1# #11#}))
                      (cs-x . (#%decode-syntax {wrap cs-x #28# #1# #11#}))
                      (cs-x-type
                       .
                       (#%decode-syntax {wrap cs-x-type #28# #1# #11#}))
                      (cs-y . (#%decode-syntax {wrap cs-y #28# #1# #11#}))
                      (cs-y-type
                       .
                       (#%decode-syntax {wrap cs-y-type #28# #1# #11#}))
                      (^TYPE-tag.0
                       .
                       (#%decode-syntax
                        {wrap
                         ^TYPE-tag
                         #29=#(struct:srcloc
                               ".../ffi/unsafe.rkt"
                               1553
                               35
                               69057
                               6)
                         #1#
                         #30=#s((wrap zo 0)
                                (#s((module-shift zo 0) #20# #8# insp0 insp0)
                                 #s((module-shift zo 0)
                                    {#%modidx #f #f}
                                    #20#
                                    #f
                                    #f))
                                (#14# . #18#)
                                ((#3# 0) (#22# 0)))}))
                      (cs? . (#%decode-syntax {wrap cs? #28# #1# #11#}))
                      (^TYPE?.0
                       .
                       (#%decode-syntax {wrap ^TYPE? #29# #1# #30#}))
                      (list*->cs
                       .
                       (#%decode-syntax {wrap list*->cs #28# #1# #11#}))
                      (_^TYPE.0
                       .
                       (#%decode-syntax {wrap _^TYPE #29# #1# #30#}))
                      (_^TYPE/null.0
                       .
                       (#%decode-syntax {wrap _^TYPE/null #29# #1# #30#}))
                      (list->cs
                       .
                       (#%decode-syntax {wrap list->cs #28# #1# #11#}))
                      (alignment-v.0
                       .
                       (#%decode-syntax
                        {wrap
                         alignment-v
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1560 21 69444 11)
                         #1#
                         #30#}))
                      (make-cs
                       .
                       (#%decode-syntax {wrap make-cs #28# #1# #11#}))
                      (all-offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1575 39 70280 11)
                         #1#
                         #30#}))
                      (all-tags.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-tags
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1563 21 69639 8)
                         #1#
                         #30#}))
                      (set-cs-x!
                       .
                       (#%decode-syntax {wrap set-cs-x! #28# #1# #11#}))
                      (all-types.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1575 29 70270 9)
                         #1#
                         #30#}))
                      (set-cs-y!
                       .
                       (#%decode-syntax {wrap set-cs-y! #28# #1# #11#}))
                      (list*->super.0
                       .
                       (#%decode-syntax
                        {wrap
                         list*->super
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1549 56 68811 12)
                         #1#
                         #30#}))
                      (offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1561 21 69487 7)
                         #1#
                         #30#}))
                      (struct:cpointer:super.0
                       .
                       (#%decode-syntax
                        {wrap
                         struct:cpointer:super
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1550 43 68866 21)
                         #1#
                         #30#}))
                      (super->list*.0
                       .
                       (#%decode-syntax
                        {wrap
                         super->list*
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1549 43 68798 12)
                         #1#
                         #30#}))
                      (N
                       .
                       (#%decode-syntax
                        {wrap
                         N
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           10
                           9
                           152
                           1)
                         #1#
                         #11#}))
                      (super-offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 66 68742 13)
                         #1#
                         #30#}))
                      (super-pointer.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-pointer
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 29 68705 13)
                         #1#
                         #30#}))
                      (super-tags.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-tags
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 43 68719 10)
                         #1#
                         #30#}))
                      (super-types.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 54 68730 11)
                         #1#
                         #30#}))
                      (test-check-fun
                       .
                       (#%decode-syntax
                        {wrap
                         test-check-fun
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           19
                           10
                           343
                           14)
                         #1#
                         #11#}))
                      (super-wrap-type-type.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-wrap-type-type
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1550 65 68888 20)
                         #1#
                         #30#}))
                      (test-fun
                       .
                       (#%decode-syntax
                        {wrap
                         test-fun
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           11
                           10
                           171
                           8)
                         #1#
                         #11#}))
                      (types.0
                       .
                       (#%decode-syntax
                        {wrap
                         types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1559 21 69400 5)
                         #1#
                         #30#}))
                      (_cs . (#%decode-syntax {wrap _cs #28# #1# #11#}))
                      (test-unsafe-fun
                       .
                       (#%decode-syntax
                        {wrap
                         test-unsafe-fun
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           33
                           10
                           677
                           15)
                         #1#
                         #11#}))
                      (unsafe-cs-x1.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-x1
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#31=#s((scope #(2 3 4) zo 0)
                                    8
                                    macro
                                    ((unsafe-cs-x1
                                      (#31# . #13#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-cs-x1.0))))
                                    ()
                                    #f)
                             .
                             #26#)
                            ((#3# 0)))}))
                      (_cs-pointer
                       .
                       (#%decode-syntax {wrap _cs-pointer #28# #1# #11#}))
                      (unsafe-cs-y2.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-y2
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#32=#s((scope #(2 3 4) zo 0)
                                    9
                                    macro
                                    ((unsafe-cs-y2
                                      (#32# . #13#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-cs-y2.0))))
                                    ()
                                    #f)
                             .
                             #26#)
                            ((#3# 0)))}))
                      (_cs-pointer/null
                       .
                       (#%decode-syntax {wrap _cs-pointer/null #28# #1# #11#}))
                      (unsafe-cs-x
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-x
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           29
                           10
                           565
                           11)
                         #1#
                         #11#}))
                      (unsafe-set-cs-x!3.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-set-cs-x!3
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#33=#s((scope #(2 3 4) zo 0)
                                    10
                                    macro
                                    ((unsafe-set-cs-x!3
                                      (#33# . #13#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-set-cs-x!3.0))))
                                    ()
                                    #f)
                             .
                             #26#)
                            ((#3# 0)))}))
                      (unsafe-set-cs-y!4.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-set-cs-y!4
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#34=#s((scope #(2 3 4) zo 0)
                                    11
                                    macro
                                    ((unsafe-set-cs-y!4
                                      (#34# . #13#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-set-cs-y!4.0))))
                                    ()
                                    #f)
                             .
                             #26#)
                            ((#3# 0)))}))))))
    (quote language-info #f)
    (require (lib "racket/base.rkt")
             (lib "racket/flonum.rkt")
             (lib "ffi/unsafe.rkt")
             (lib "racket/unsafe/ops.rkt"))
    (provide)
    (quote inspector insp0)
    (module configure-runtime ....
      (quote self {#%modidx #f #f})
      (quote internal-context #t)
      (quote bindings #35=#hasheq())
      (quote language-info #f)
      (require #36='#%kernel (lib "racket/runtime-config.rkt"))
      (provide)
      (quote inspector insp0)
      (print-as-expression '#t))
    (begin
      (define-syntaxes
       (cs)
       (let ()
         (quote inspector insp0)
         (define stx32 (#%decode-syntax {wrap make-cs #28# #1# #11#}))
         (define stx33 (#%decode-syntax {wrap cs? #28# #1# #11#}))
         (define stx34 (#%decode-syntax {wrap cs-x #28# #1# #11#}))
         (define stx35 (#%decode-syntax {wrap cs-y #28# #1# #11#}))
         (define stx36 (#%decode-syntax {wrap set-cs-x! #28# #1# #11#}))
         (define stx37 (#%decode-syntax {wrap set-cs-y! #28# #1# #11#}))
         (|_make-struct-info@(lib "racket/private/struct-info.rkt")|
          (lambda ()
            '...s/ffi/unsafe.rkt:1540:15
            '(flags: preserves-marks single-result)
            '(captures:
              (val/ref #%globals)
              (|_alt-reverse:f@(lib "racket/private/reverse.rkt")| #%syntax))
            (list
             '#f
             stx32
             stx33
             (|_alt-reverse:f@(lib "racket/private/reverse.rkt")|
              (list stx34 stx35))
             (|_alt-reverse:f@(lib "racket/private/reverse.rkt")|
              (list stx36 stx37))
             '#t))))))
    (#%apply-values
     |_print-values:p@(lib "racket/private/modbeg.rkt")|
     (printf '"ping\n"))
    (define-values
     (_super-pointer.0
      _super-tags.0
      _super-types.0
      _super-offsets.0
      _super->list*.0
      _list*->super.0
      _struct:cpointer:super.0
      _super-wrap-type-type.0)
     (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
      _double
      (#%closed
       ...s/ffi/unsafe.rkt:1494:2723
       (lambda ()
         '...s/ffi/unsafe.rkt:1494:27
         (values '#f '() '#f '#f '#f '#f '#f values)))))
    (define-values (_^TYPE-tag.0) '^TYPE)
    (define-values
     (__^TYPE.0)
     (|__cpointer:f@(lib "ffi/unsafe.rkt")|
      '^TYPE
      (#%checked _super-pointer.0)
      '#f
      '#f))
    (define-values
     (__^TYPE/null.0)
     (|__cpointer/null:f@(lib "ffi/unsafe.rkt")|
      '^TYPE
      (#%checked _super-pointer.0)
      '#f
      '#f))
    (define-values
     (_^TYPE?.0)
     (lambda (arg0-70)
       '^TYPE?
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")|))
       (if (cpointer? arg0-70)
         (let ((local72 (cpointer-tag (#%sfs-clear arg0-70))))
           (if (pair? local72)
             (if (null? (unsafe-cdr local72))
               (eq? '^TYPE (unsafe-car local72))
               (if (|_memq@(lib "racket/private/member.rkt")|
                    '^TYPE
                    (#%sfs-clear local72))
                 '#t
                 '#f))
             (eq? '^TYPE local72)))
         '#f)))
    (define-values
     (_wrap-cs-type)
     (|_new:procedure-rename:p@(lib "racket/private/kw.rkt")|
      _super-wrap-type-type.0
      'wrap-cs-type))
    (define-values (__cs-pointer) (_wrap-cs-type __^TYPE.0))
    (define-values (__cs-pointer/null) (_wrap-cs-type __^TYPE/null.0))
    (define-values (_cs-x-type) _double)
    (define-values (_cs-y-type) _double)
    (define-values (_types.0) (list _double _double))
    (define-values (_alignment-v.0) '#f)
    (define-values
     (_offsets.0)
     (|_compute-offsets:p@(lib "ffi/unsafe.rkt")| _types.0 '#f (list '#f '#f)))
    (define-values (_x-offset5.0 _y-offset6.0) (apply values _offsets.0))
    (define-values (_all-tags.0) (cons '^TYPE (#%checked _super-tags.0)))
    (define-values
     (__cs)
     (let ((local99 (make-cstruct-type _types.0 '#f '#f)))
       (let ((local103 (|__cpointer:f@(lib "ffi/unsafe.rkt")| '^TYPE local99)))
         (let ((local106 (ctype-c->scheme local103)))
           (_wrap-cs-type
            (make-ctype
             (#%sfs-clear local99)
             (ctype-scheme->c (#%sfs-clear local103))
             (begin0
               (lambda (arg0-113)
                 '...s/ffi/unsafe.rkt:1572:29
                 '(flags: preserves-marks single-result)
                 '(captures:
                   (val/ref local106)
                   (val/ref #%modvars)
                   (_all-tags.0))
                 (begin
                   (if arg0-113
                     (begin
                       (#%sfs-clear local106)
                       (set-cpointer-tag! arg0-113 _all-tags.0))
                     ((#%sfs-clear local106) '#f))
                   arg0-113))
               (#%sfs-clear local106))))))))
    (define-values (_all-types.0 _all-offsets.0) (values _types.0 _offsets.0))
    (define-values
     (_unsafe-cs-x1.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-119)
         'unsafe-cs-x1
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_x-offset5.0))
         (ptr-ref arg0-119 _double 'abs (#%checked _x-offset5.0)))
       (lambda (arg0-124)
         'unsafe-cs-x1
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_x-offset5.0))
         (ptr-ref
          (#%sfs-clear arg0-124)
          _double
          'abs
          (#%checked _x-offset5.0)))))
    (define-values
     (_cs-x)
     (lambda (arg0-129)
       'cs-x
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")| _x-offset5.0))
       (begin
         (if (if (cpointer? arg0-129)
               (let ((local131 (cpointer-tag arg0-129)))
                 (if (pair? local131)
                   (if (null? (unsafe-cdr local131))
                     (eq? '^TYPE (unsafe-car local131))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local131)))
                   (eq? '^TYPE local131)))
               '#f)
           '#<void>
           (raise-argument-error 'cs-x '"cs?" arg0-129))
         (ptr-ref
          (#%sfs-clear arg0-129)
          _double
          'abs
          (#%checked _x-offset5.0)))))
    (define-values
     (_unsafe-cs-y2.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-150)
         'unsafe-cs-y2
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_y-offset6.0))
         (ptr-ref arg0-150 _double 'abs _y-offset6.0))
       (lambda (arg0-155)
         'unsafe-cs-y2
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_y-offset6.0))
         (ptr-ref (#%sfs-clear arg0-155) _double 'abs _y-offset6.0))))
    (define-values
     (_cs-y)
     (lambda (arg0-160)
       'cs-y
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")| _y-offset6.0))
       (begin
         (if (if (cpointer? arg0-160)
               (let ((local162 (cpointer-tag arg0-160)))
                 (if (pair? local162)
                   (if (null? (unsafe-cdr local162))
                     (eq? '^TYPE (unsafe-car local162))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local162)))
                   (eq? '^TYPE local162)))
               '#f)
           '#<void>
           (raise-argument-error 'cs-y '"cs?" arg0-160))
         (ptr-ref (#%sfs-clear arg0-160) _double 'abs _y-offset6.0))))
    (define-values
     (_unsafe-set-cs-x!3.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-181 arg1-182)
         'unsafe-set-cs-x!3
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_x-offset5.0))
         (ptr-set! arg0-181 _double 'abs (#%checked _x-offset5.0) arg1-182))
       (lambda (arg0-188 arg1-189)
         'unsafe-set-cs-x!3
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_x-offset5.0))
         (ptr-set!
          (#%sfs-clear arg0-188)
          _double
          'abs
          (#%checked _x-offset5.0)
          (#%sfs-clear arg1-189)))))
    (define-values
     (_set-cs-x!)
     (lambda (arg0-195 arg1-196)
       'set-cs-x!
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")| _x-offset5.0))
       (begin
         (if (if (cpointer? arg0-195)
               (let ((local198 (cpointer-tag arg0-195)))
                 (if (pair? local198)
                   (if (null? (unsafe-cdr local198))
                     (eq? '^TYPE (unsafe-car local198))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local198)))
                   (eq? '^TYPE local198)))
               '#f)
           '#<void>
           (raise-argument-error 'set-cs-x! '"cs?" '0 arg0-195 arg1-196))
         (ptr-set!
          (#%sfs-clear arg0-195)
          _double
          'abs
          (#%checked _x-offset5.0)
          (#%sfs-clear arg1-196)))))
    (define-values
     (_unsafe-set-cs-y!4.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-220 arg1-221)
         'unsafe-set-cs-y!4
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_y-offset6.0))
         (ptr-set! arg0-220 _double 'abs _y-offset6.0 arg1-221))
       (lambda (arg0-227 arg1-228)
         'unsafe-set-cs-y!4
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_y-offset6.0))
         (ptr-set!
          (#%sfs-clear arg0-227)
          _double
          'abs
          _y-offset6.0
          (#%sfs-clear arg1-228)))))
    (define-values
     (_set-cs-y!)
     (lambda (arg0-234 arg1-235)
       'set-cs-y!
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")| _y-offset6.0))
       (begin
         (if (if (cpointer? arg0-234)
               (let ((local237 (cpointer-tag arg0-234)))
                 (if (pair? local237)
                   (if (null? (unsafe-cdr local237))
                     (eq? '^TYPE (unsafe-car local237))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local237)))
                   (eq? '^TYPE local237)))
               '#f)
           '#<void>
           (raise-argument-error 'set-cs-y! '"cs?" '0 arg0-234 arg1-235))
         (ptr-set!
          (#%sfs-clear arg0-234)
          _double
          'abs
          _y-offset6.0
          (#%sfs-clear arg1-235)))))
    (define-values
     (_make-cs)
     (lambda (arg0-259 arg1-260)
       'make-cs
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_x-offset5.0 _y-offset6.0 _all-tags.0 __cs))
       (let ((local261 (malloc __cs 'atomic)))
         (begin
           (set-cpointer-tag! local261 _all-tags.0)
           (ptr-set!
            local261
            _double
            'abs
            (#%checked _x-offset5.0)
            (#%sfs-clear arg0-259))
           (ptr-set! local261 _double 'abs _y-offset6.0 (#%sfs-clear arg1-260))
           local261))))
    (define-values
     (_list->cs)
     (begin
       '%%inline-variant%%
       (lambda (arg0-276)
         'list->cs
         '(captures: (val/ref #%modvars) (_make-cs))
         (apply _make-cs arg0-276))
       (lambda (arg0-279)
         'list->cs
         '(captures: (val/ref #%modvars) (_make-cs))
         (apply _make-cs (#%sfs-clear arg0-279)))))
    (define-values
     (_list*->cs)
     (lambda (arg0-282)
       'list*->cs
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
          |_memq@(lib "racket/private/member.rkt")|
          _all-tags.0
          __cs
          _all-types.0
          _all-offsets.0))
       (if (if (cpointer? arg0-282)
             (let ((local284 (cpointer-tag arg0-282)))
               (if (pair? local284)
                 (if (null? (unsafe-cdr local284))
                   (eq? '^TYPE (unsafe-car local284))
                   (|_memq@(lib "racket/private/member.rkt")|
                    '^TYPE
                    (#%sfs-clear local284)))
                 (eq? '^TYPE local284)))
             '#f)
         arg0-282
         (if (= (length arg0-282) (length (#%checked _all-types.0)))
           (let ((local300 (malloc __cs 'atomic)))
             (begin
               (set-cpointer-tag! local300 _all-tags.0)
               (let ((...s/ffi/unsafe.rkt:1626:20305
                      (lambda (arg0-306 arg1-307 arg2-308)
                        '...s/ffi/unsafe.rkt:1626:20
                        '(flags: preserves-marks single-result)
                        '(captures:
                          (val/ref local300)
                          (val/ref #%modvars)
                          (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|))
                        (let ((localv309 ?)
                              (localv310 ?)
                              (localv311 ?)
                              (localv312 ?)
                              (localv313 ?)
                              (localv314 ?)
                              (localv315 ?)
                              (localv316 ?))
                          (begin
                            (set!-values (localv309
                                          localv310
                                          localv311
                                          localv312
                                          localv313
                                          localv314
                                          localv315
                                          localv316)
                              (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                               arg0-306
                               (#%closed
                                ...s/ffi/unsafe.rkt:1631:2917
                                (lambda ()
                                  '...s/ffi/unsafe.rkt:1631:29
                                  (values
                                   '#f
                                   '()
                                   '#f
                                   '#f
                                   '#f
                                   '#f
                                   '#f
                                   values)))))
                            (begin
                              (#%sfs-clear localv316)
                              (#%sfs-clear localv315)
                              (#%sfs-clear localv313)
                              (#%sfs-clear localv312)
                              (#%sfs-clear localv311)
                              (#%sfs-clear localv310)
                              (#%sfs-clear localv309)
                              (ptr-set!
                               (#%sfs-clear local300)
                               (#%sfs-clear arg0-306)
                               'abs
                               (#%sfs-clear arg1-307)
                               (if localv314
                                 ((#%sfs-clear localv314)
                                  (#%sfs-clear arg2-308))
                                 (begin
                                   (#%sfs-clear localv314)
                                   (#%sfs-clear arg2-308))))))))))
                 (for-each
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1626:20305)
                  (#%checked _all-types.0)
                  _all-offsets.0
                  (#%sfs-clear arg0-282)))
               local300))
           (error
            '_cs
            '"expecting ~s values, got ~s: ~e"
            (length (#%checked _all-types.0))
            (length arg0-282)
            (#%sfs-clear arg0-282))))))
    (define-values
     (_cs->list)
     (lambda (arg0-344)
       'cs->list
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")|
          _all-types.0
          _all-offsets.0))
       (begin
         (if (if (cpointer? arg0-344)
               (let ((local346 (cpointer-tag arg0-344)))
                 (if (pair? local346)
                   (if (null? (unsafe-cdr local346))
                     (eq? '^TYPE (unsafe-car local346))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local346)))
                   (eq? '^TYPE local346)))
               '#f)
           '#<void>
           (raise-argument-error 'TYPE-list '"cs?" arg0-344))
         (let ((...s/ffi/unsafe.rkt:1641:19361
                (lambda (arg0-362 arg1-363)
                  '...s/ffi/unsafe.rkt:1641:19
                  '(flags: preserves-marks single-result)
                  '(captures: (val/ref arg0-344))
                  (ptr-ref
                   (#%sfs-clear arg0-344)
                   (#%sfs-clear arg0-362)
                   'abs
                   (#%sfs-clear arg1-363)))))
           (let ((local368 (#%checked _all-types.0)))
             (if (if (list? local368)
                   (if (list? _all-offsets.0)
                     (= (length local368) (length _all-offsets.0))
                     '#f)
                   '#f)
               ((#%closed
                 loop18
                 (lambda (arg0-378 arg1-379 arg2-380)
                   'loop
                   '(flags: preserves-marks single-result)
                   (if (null? arg1-379)
                     '()
                     (cons
                      (ptr-ref arg0-378 (car arg1-379) 'abs (car arg2-380))
                      (let ((local390 (unsafe-cdr (#%sfs-clear arg1-379))))
                        (let ((local392 (unsafe-cdr (#%sfs-clear arg2-380))))
                          (if (null? local390)
                            '()
                            (cons
                             (ptr-ref
                              arg0-378
                              (car local390)
                              'abs
                              (car local392))
                             (let ((local403
                                    (unsafe-cdr (#%sfs-clear local390))))
                               (let ((local405
                                      (unsafe-cdr (#%sfs-clear local392))))
                                 (if (null? local403)
                                   '()
                                   (cons
                                    (ptr-ref
                                     arg0-378
                                     (car local403)
                                     'abs
                                     (car local405))
                                    (loop18
                                     (#%sfs-clear arg0-378)
                                     (unsafe-cdr (#%sfs-clear local403))
                                     (unsafe-cdr
                                      (#%sfs-clear local405)))))))))))))))
                arg0-344
                local368
                _all-offsets.0)
               (begin
                 (#%sfs-clear arg0-344)
                 (map
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1641:19361)
                  (#%sfs-clear local368)
                  _all-offsets.0))))))))
    (define-values
     (lift28)
     (lambda (arg0-424 arg1-425 arg2-426 arg3-427)
       'loop
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")| lift28))
       (if (null? arg2-426)
         '()
         (cons
          (let ((local431 (car arg2-426)))
            (let ((localv433 ?)
                  (localv434 ?)
                  (localv435 ?)
                  (localv436 ?)
                  (localv437 ?)
                  (localv438 ?)
                  (localv439 ?)
                  (localv440 ?)
                  (localv441 ?))
              (begin
                (set!-values (localv433)
                  (ptr-ref arg1-425 local431 'abs (car arg3-427)))
                (begin
                  (set!-values (localv434
                                localv435
                                localv436
                                localv437
                                localv438
                                localv439
                                localv440
                                localv441)
                    (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                     (#%sfs-clear local431)
                     (#%closed
                      ...s/ffi/unsafe.rkt:1652:2819
                      (lambda ()
                        '...s/ffi/unsafe.rkt:1652:28
                        (values '#f '() '#f '#f '#f '#f '#f values)))))
                  (begin
                    (#%sfs-clear localv441)
                    (#%sfs-clear localv440)
                    (#%sfs-clear localv439)
                    (#%sfs-clear localv437)
                    (#%sfs-clear localv436)
                    (#%sfs-clear localv435)
                    (#%sfs-clear localv434)
                    (if localv438
                      ((#%sfs-clear localv438) (#%sfs-clear localv433))
                      localv433))))))
          (let ((local458 (unsafe-cdr (#%sfs-clear arg2-426))))
            (let ((local460 (unsafe-cdr (#%sfs-clear arg3-427))))
              (if (null? local458)
                '()
                (cons
                 (let ((local465 (car local458)))
                   (let ((localv467 ?)
                         (localv468 ?)
                         (localv469 ?)
                         (localv470 ?)
                         (localv471 ?)
                         (localv472 ?)
                         (localv473 ?)
                         (localv474 ?)
                         (localv475 ?))
                     (begin
                       (set!-values (localv467)
                         (ptr-ref arg1-425 local465 'abs (car local460)))
                       (begin
                         (set!-values (localv468
                                       localv469
                                       localv470
                                       localv471
                                       localv472
                                       localv473
                                       localv474
                                       localv475)
                           (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                            (#%sfs-clear local465)
                            (#%closed
                             ...s/ffi/unsafe.rkt:1652:2820
                             (lambda ()
                               '...s/ffi/unsafe.rkt:1652:28
                               (values '#f '() '#f '#f '#f '#f '#f values)))))
                         (begin
                           (#%sfs-clear localv475)
                           (#%sfs-clear localv474)
                           (#%sfs-clear localv473)
                           (#%sfs-clear localv471)
                           (#%sfs-clear localv470)
                           (#%sfs-clear localv469)
                           (#%sfs-clear localv468)
                           (if localv472
                             ((#%sfs-clear localv472) (#%sfs-clear localv467))
                             localv467))))))
                 (let ((local492 (unsafe-cdr (#%sfs-clear local458))))
                   (let ((local494 (unsafe-cdr (#%sfs-clear local460))))
                     (if (null? local492)
                       '()
                       (cons
                        (arg0-424 (car local492) (car local494))
                        (lift28
                         (#%sfs-clear arg0-424)
                         (#%sfs-clear arg1-425)
                         (unsafe-cdr (#%sfs-clear local492))
                         (unsafe-cdr (#%sfs-clear local494)))))))))))))))
    (define-values
     (_cs->list*)
     (lambda (arg0-509)
       'cs->list*
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
          |_memq@(lib "racket/private/member.rkt")|
          _all-types.0
          _all-offsets.0
          lift28))
       (begin
         (if (if (cpointer? arg0-509)
               (let ((local511 (cpointer-tag arg0-509)))
                 (if (pair? local511)
                   (if (null? (unsafe-cdr local511))
                     (eq? '^TYPE (unsafe-car local511))
                     (|_memq@(lib "racket/private/member.rkt")|
                      '^TYPE
                      (#%sfs-clear local511)))
                   (eq? '^TYPE local511)))
               '#f)
           '#<void>
           (raise-argument-error 'TYPE-list '"cs?" arg0-509))
         (let ((...s/ffi/unsafe.rkt:1646:19526
                (lambda (arg0-527 arg1-528)
                  '...s/ffi/unsafe.rkt:1646:19
                  '(captures:
                    (val/ref arg0-509)
                    (val/ref #%modvars)
                    (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|))
                  (let ((localv529 ?)
                        (localv530 ?)
                        (localv531 ?)
                        (localv532 ?)
                        (localv533 ?)
                        (localv534 ?)
                        (localv535 ?)
                        (localv536 ?)
                        (localv537 ?))
                    (begin
                      (set!-values (localv529)
                        (ptr-ref
                         (#%sfs-clear arg0-509)
                         arg0-527
                         'abs
                         (#%sfs-clear arg1-528)))
                      (begin
                        (set!-values (localv530
                                      localv531
                                      localv532
                                      localv533
                                      localv534
                                      localv535
                                      localv536
                                      localv537)
                          (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                           (#%sfs-clear arg0-527)
                           (#%closed
                            ...s/ffi/unsafe.rkt:1652:2821
                            (lambda ()
                              '...s/ffi/unsafe.rkt:1652:28
                              (values '#f '() '#f '#f '#f '#f '#f values)))))
                        (begin
                          (#%sfs-clear localv537)
                          (#%sfs-clear localv536)
                          (#%sfs-clear localv535)
                          (#%sfs-clear localv533)
                          (#%sfs-clear localv532)
                          (#%sfs-clear localv531)
                          (#%sfs-clear localv530)
                          (if localv534
                            ((#%sfs-clear localv534) (#%sfs-clear localv529))
                            localv529))))))))
           (let ((local553 (#%checked _all-types.0)))
             (if (if (list? local553)
                   (if (list? _all-offsets.0)
                     (= (length local553) (length _all-offsets.0))
                     '#f)
                   '#f)
               (lift28
                ...s/ffi/unsafe.rkt:1646:19526
                arg0-509
                local553
                _all-offsets.0)
               (begin
                 (#%sfs-clear arg0-509)
                 (map
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1646:19526)
                  (#%sfs-clear local553)
                  _all-offsets.0))))))))
    (#%apply-values
     |_print-values:p@(lib "racket/private/modbeg.rkt")|
     (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
      __cs
      'set!
      __^TYPE.0
      _all-tags.0
      (#%checked _all-types.0)
      _all-offsets.0
      _cs->list*
      _list*->cs
      (#%checked _struct:cpointer:super.0)
      _wrap-cs-type))
    (define-values (_cs?) _^TYPE?.0)
    (define-values (_cs-tag) '^TYPE)
    (define-values (_N) '180000)
    (define-values
     (lift29)
     (lambda (arg0-577 argflonum1-578 arg2-579)
       '#(for-loop
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          13
          2
          215
          116
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")|
          _x-offset5.0
          _y-offset6.0
          _cs-x
          _cs-y
          lift29))
       (if (< arg2-579 '180000)
         (let ((flonum582
                (fl+
                 argflonum1-578
                 (fl+
                  (begin
                    (if (if (cpointer? arg0-577)
                          (let ((local588 (cpointer-tag arg0-577)))
                            (if (pair? local588)
                              (if (null? (unsafe-cdr local588))
                                (eq? '^TYPE (unsafe-car local588))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 '^TYPE
                                 (#%sfs-clear local588)))
                              (eq? '^TYPE local588)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-x '"cs?" arg0-577))
                    (ptr-ref arg0-577 _double 'abs (#%checked _x-offset5.0)))
                  (begin
                    (if (if (cpointer? arg0-577)
                          (let ((local608 (cpointer-tag arg0-577)))
                            (if (pair? local608)
                              (if (null? (unsafe-cdr local608))
                                (eq? '^TYPE (unsafe-car local608))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 '^TYPE
                                 (#%sfs-clear local608)))
                              (eq? '^TYPE local608)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-y '"cs?" arg0-577))
                    (ptr-ref arg0-577 _double 'abs _y-offset6.0))))))
           (let ((local627 (+ (#%sfs-clear arg2-579) '1)))
             (if (< local627 '180000)
               (let ((flonum632
                      (fl+ flonum582 (fl+ (_cs-x arg0-577) (_cs-y arg0-577)))))
                 (let ((local639 (+ (#%sfs-clear local627) '1)))
                   (if (< local639 '180000)
                     (let ((flonum644
                            (fl+
                             flonum632
                             (fl+ (_cs-x arg0-577) (_cs-y arg0-577)))))
                       (let ((local651 (+ (#%sfs-clear local639) '1)))
                         (if (< local651 '180000)
                           (lift29
                            arg0-577
                            (fl+
                             flonum644
                             (fl+
                              (_cs-x arg0-577)
                              (_cs-y (#%sfs-clear arg0-577))))
                            (+ local651 '1))
                           flonum644)))
                     flonum632)))
               flonum582)))
         argflonum1-578)))
    (define-values
     (_test-fun)
     (lambda ()
       '#(test-fun
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          11
          0
          162
          170
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_x-offset5.0 _y-offset6.0 _all-tags.0 __cs lift29))
       (let ((local667
              (let ((local668 (malloc __cs 'atomic)))
                (begin
                  (set-cpointer-tag! local668 _all-tags.0)
                  (ptr-set!
                   local668
                   _double
                   'abs
                   (#%checked _x-offset5.0)
                   '1.0)
                  (ptr-set! local668 _double 'abs _y-offset6.0 '2.0)
                  local668))))
         (lift29 local667 '0.0 '0))))
    (define-values
     (lift30)
     (lambda (arg0-686 argflonum1-687 arg2-688)
       '#(for-loop
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          23
          2
          437
          116
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")|
          _x-offset5.0
          _y-offset6.0
          _cs-x
          _cs-y
          lift30))
       (if (< arg2-688 '180000)
         (let ((flonum691
                (fl+
                 argflonum1-687
                 (fl+
                  (begin
                    (if (if (cpointer? arg0-686)
                          (let ((local697 (cpointer-tag arg0-686)))
                            (if (pair? local697)
                              (if (null? (unsafe-cdr local697))
                                (eq? '^TYPE (unsafe-car local697))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 '^TYPE
                                 (#%sfs-clear local697)))
                              (eq? '^TYPE local697)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-x '"cs?" arg0-686))
                    (ptr-ref arg0-686 _double 'abs (#%checked _x-offset5.0)))
                  (begin
                    (if (if (cpointer? arg0-686)
                          (let ((local717 (cpointer-tag arg0-686)))
                            (if (pair? local717)
                              (if (null? (unsafe-cdr local717))
                                (eq? '^TYPE (unsafe-car local717))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 '^TYPE
                                 (#%sfs-clear local717)))
                              (eq? '^TYPE local717)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-y '"cs?" arg0-686))
                    (ptr-ref arg0-686 _double 'abs _y-offset6.0))))))
           (let ((local736 (+ (#%sfs-clear arg2-688) '1)))
             (if (< local736 '180000)
               (let ((flonum741
                      (fl+ flonum691 (fl+ (_cs-x arg0-686) (_cs-y arg0-686)))))
                 (let ((local748 (+ (#%sfs-clear local736) '1)))
                   (if (< local748 '180000)
                     (let ((flonum753
                            (fl+
                             flonum741
                             (fl+ (_cs-x arg0-686) (_cs-y arg0-686)))))
                       (let ((local760 (+ (#%sfs-clear local748) '1)))
                         (if (< local760 '180000)
                           (lift30
                            arg0-686
                            (fl+
                             flonum753
                             (fl+
                              (_cs-x arg0-686)
                              (_cs-y (#%sfs-clear arg0-686))))
                            (+ local760 '1))
                           flonum753)))
                     flonum741)))
               flonum691)))
         argflonum1-687)))
    (define-values
     (_test-check-fun)
     (lambda ()
       '#(test-check-fun
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          19
          0
          334
          220
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_memq@(lib "racket/private/member.rkt")|
          _x-offset5.0
          _y-offset6.0
          _all-tags.0
          __cs
          lift30))
       (let ((local776
              (let ((local777 (malloc __cs 'atomic)))
                (begin
                  (set-cpointer-tag! local777 _all-tags.0)
                  (ptr-set!
                   local777
                   _double
                   'abs
                   (#%checked _x-offset5.0)
                   '1.0)
                  (ptr-set! local777 _double 'abs _y-offset6.0 '2.0)
                  local777))))
         (begin
           (if (if (cpointer? local776)
                 (let ((local793 (cpointer-tag local776)))
                   (if (pair? local793)
                     (if (null? (unsafe-cdr local793))
                       (eq? '^TYPE (unsafe-car local793))
                       (|_memq@(lib "racket/private/member.rkt")|
                        '^TYPE
                        (#%sfs-clear local793)))
                     (eq? '^TYPE local793)))
                 '#f)
             '#<void>
             (error 'impossible))
           (lift30 local776 '0.0 '0)))))
    (define-values
     (_unsafe-cs-x)
     (begin
       '%%inline-variant%%
       (#%closed
        unsafe-cs-x25
        (lambda (arg0-809)
          '#(unsafe-cs-x
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             29
             0
             556
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref arg0-809 _double 'abs '0)))
       (#%closed
        unsafe-cs-x24
        (lambda (arg0-814)
          '#(unsafe-cs-x
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             29
             0
             556
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref (#%sfs-clear arg0-814) _double 'abs '0)))))
    (define-values
     (_unsafe-cs-y)
     (begin
       '%%inline-variant%%
       (#%closed
        unsafe-cs-y27
        (lambda (arg0-819)
          '#(unsafe-cs-y
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             31
             0
             612
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref arg0-819 _double 'abs '8)))
       (#%closed
        unsafe-cs-y26
        (lambda (arg0-824)
          '#(unsafe-cs-y
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             31
             0
             612
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref (#%sfs-clear arg0-824) _double 'abs '8)))))
    (define-values
     (_test-unsafe-fun)
     (lambda ()
       '#(test-unsafe-fun
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          33
          0
          668
          191
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_x-offset5.0 _y-offset6.0 _all-tags.0 __cs))
       (let ((local829
              (let ((local830 (malloc __cs 'atomic)))
                (begin
                  (set-cpointer-tag! local830 _all-tags.0)
                  (ptr-set!
                   local830
                   _double
                   'abs
                   (#%checked _x-offset5.0)
                   '1.0)
                  (ptr-set! local830 _double 'abs _y-offset6.0 '2.0)
                  local830))))
         (let ((flonum845
                (fl+
                 '0.0
                 (fl+
                  (ptr-ref local829 _double 'abs '0)
                  (ptr-ref local829 _double 'abs '8)))))
           (let ((flonum858
                  (fl+
                   flonum845
                   (fl+
                    (ptr-ref local829 _double 'abs '0)
                    (ptr-ref local829 _double 'abs '8)))))
             (let ((flonum871
                    (fl+
                     flonum858
                     (fl+
                      (ptr-ref local829 _double 'abs '0)
                      (ptr-ref local829 _double 'abs '8)))))
               ((#%closed
                 for-loop22
                 (lambda (arg0-887 argflonum1-888 arg2-889)
                   '#(for-loop
                      #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                      35
                      2
                      728
                      130
                      #f)
                   '(flags: preserves-marks single-result)
                   (if (< arg2-889 '180000)
                     (let ((flonum892
                            (fl+
                             argflonum1-888
                             (fl+
                              (ptr-ref arg0-887 _double 'abs '0)
                              (ptr-ref arg0-887 _double 'abs '8)))))
                       (let ((local905 (+ (#%sfs-clear arg2-889) '1)))
                         (if (< local905 '180000)
                           (let ((flonum910
                                  (fl+
                                   flonum892
                                   (fl+
                                    (ptr-ref arg0-887 _double 'abs '0)
                                    (ptr-ref arg0-887 _double 'abs '8)))))
                             (let ((local923 (+ (#%sfs-clear local905) '1)))
                               (if (< local923 '180000)
                                 (let ((flonum928
                                        (fl+
                                         flonum910
                                         (fl+
                                          (ptr-ref arg0-887 _double 'abs '0)
                                          (ptr-ref
                                           arg0-887
                                           _double
                                           'abs
                                           '8)))))
                                   (let ((local941
                                          (+ (#%sfs-clear local923) '1)))
                                     (if (< local941 '180000)
                                       (for-loop22
                                        arg0-887
                                        (fl+
                                         flonum928
                                         (fl+
                                          (ptr-ref arg0-887 _double 'abs '0)
                                          (ptr-ref
                                           (#%sfs-clear arg0-887)
                                           _double
                                           'abs
                                           '8)))
                                        (+ local941 '1))
                                       flonum928)))
                                 flonum910)))
                           flonum892)))
                     argflonum1-888)))
                local829
                (fl+
                 flonum871
                 (fl+
                  (ptr-ref local829 _double 'abs '0)
                  (ptr-ref (#%sfs-clear local829) _double 'abs '8)))
                '4)))))))
    (module*
     main
     ....
     (quote self #37={#%modidx #f #f})
     (quote
      internal-context
      (#%decode-syntax
       {wrap
        #({wrap
           #t
           #1#
           #s((wrap zo 0)
              (#s((module-shift zo 0)
                  #38={#%modidx #f #f}
                  {#%modidx #39=(submod "..") #37#}
                  #f
                  #f)
               #s((module-shift zo 0) {#%modidx #f #f} #38# #f #f))
              (#s((scope #(2 3 4) zo 0) 3 module () () #f)
               .
               #40=(#s((scope #(2 3 4) zo 0) 0 module () () #f)))
              ((#41=#s((multi-scope #(2) zo 0) 8 (cstruct main) ()) 0)
               (#42=#s((multi-scope #(2) zo 0)
                       9
                       cstruct
                       ((0
                         #43=#s((scope #(2 3 4) zo 0)
                                1
                                module
                                ((N
                                  #44=(#43# . #40#)
                                  #45=#s((module-binding binding 0 zo 0)
                                         (insp0 . #38#)))
                                 (_cs #44# #45#)
                                 (_cs-pointer #44# #45#)
                                 (_cs-pointer/null #44# #45#)
                                 (cs #44# #45#)
                                 (cs->list #44# #45#)
                                 (cs->list* #44# #45#)
                                 (cs-tag #44# #45#)
                                 (cs-x #44# #45#)
                                 (cs-x-type #44# #45#)
                                 (cs-y #44# #45#)
                                 (cs-y-type #44# #45#)
                                 (cs? #44# #45#)
                                 (list*->cs #44# #45#)
                                 (list->cs #44# #45#)
                                 (make-cs #44# #45#)
                                 (set-cs-x! #44# #45#)
                                 (set-cs-y! #44# #45#)
                                 (test-check-fun #44# #45#)
                                 (test-fun #44# #45#)
                                 (test-unsafe-fun #44# #45#)
                                 (unsafe-cs-x #44# #45#)
                                 (unsafe-cs-y #44# #45#)
                                 (wrap-cs-type #44# #45#))
                                ((#44#
                                  #s((all-from-module zo 0)
                                     #46={#%modidx racket/base #f}
                                     0
                                     0
                                     insp0
                                     ()
                                     #f))
                                 (#44#
                                  #s((all-from-module zo 0)
                                     {#%modidx racket/flonum #f}
                                     0
                                     0
                                     insp0
                                     ()
                                     #f))
                                 (#44#
                                  #s((all-from-module zo 0)
                                     {#%modidx ffi/unsafe #f}
                                     0
                                     0
                                     insp0
                                     ()
                                     #f))
                                 (#44#
                                  #s((all-from-module zo 0)
                                     {#%modidx racket/unsafe/ops #f}
                                     0
                                     0
                                     insp0
                                     ()
                                     #f)))
                                #42#))
                        (1
                         #47=#s((scope #(2 3 4) zo 0)
                                2
                                module
                                ()
                                (((#47# . #40#)
                                  #s((all-from-module zo 0)
                                     #46#
                                     1
                                     0
                                     insp0
                                     ()
                                     #f)))
                                #42#))))
                0)))}
          {wrap #f #1# #s((wrap zo 0) () () ((#41# 0)))})
        #1#
        #s((wrap zo 0) () () ())}))
     (quote bindings #35#)
     (quote language-info #f)
     (require #39#)
     (provide)
     (quote inspector insp0)
     (module configure-runtime ....
       (quote self {#%modidx #f #f})
       (quote internal-context #t)
       (quote bindings #35#)
       (quote language-info #f)
       (require #36# (lib "racket/runtime-config.rkt"))
       (provide)
       (quote inspector insp0)
       (print-as-expression '#t))
     (#%apply-values
      |_print-values:p@(lib "racket/private/modbeg.rkt")|
      (let ((localv976 ?) (localv977 ?) (localv978 ?) (localv979 ?))
        (begin
          (set!-values (localv976 localv977 localv978 localv979)
            (time-apply
             (lambda ()
               '.../more-scheme.rkt:336:52
               '(captures: (val/ref #%modvars) (|_test-fun:P@(submod "..")|))
               (|_test-fun:P@(submod "..")|))
             '()))
          (begin
            (printf
             '"cpu time: ~s real time: ~s gc time: ~s\n"
             (#%sfs-clear localv977)
             (#%sfs-clear localv978)
             (#%sfs-clear localv979))
            (apply values (#%sfs-clear localv976))))))
     (#%apply-values
      |_print-values:p@(lib "racket/private/modbeg.rkt")|
      (let ((localv988 ?) (localv989 ?) (localv990 ?) (localv991 ?))
        (begin
          (set!-values (localv988 localv989 localv990 localv991)
            (time-apply
             (lambda ()
               '.../more-scheme.rkt:336:52
               '(captures:
                 (val/ref #%modvars)
                 (|_test-check-fun:P@(submod "..")|))
               (|_test-check-fun:P@(submod "..")|))
             '()))
          (begin
            (printf
             '"cpu time: ~s real time: ~s gc time: ~s\n"
             (#%sfs-clear localv989)
             (#%sfs-clear localv990)
             (#%sfs-clear localv991))
            (apply values (#%sfs-clear localv988))))))
     (#%apply-values
      |_print-values:p@(lib "racket/private/modbeg.rkt")|
      (let ((localv1000 ?) (localv1001 ?) (localv1002 ?) (localv1003 ?))
        (begin
          (set!-values (localv1000 localv1001 localv1002 localv1003)
            (time-apply
             (lambda ()
               '.../more-scheme.rkt:336:52
               '(captures:
                 (val/ref #%modvars)
                 (|_test-unsafe-fun:P@(submod "..")|))
               (|_test-unsafe-fun:P@(submod "..")|))
             '()))
          (begin
            (printf
             '"cpu time: ~s real time: ~s gc time: ~s\n"
             (#%sfs-clear localv1001)
             (#%sfs-clear localv1002)
             (#%sfs-clear localv1003))
            (apply values (#%sfs-clear localv1000)))))))))
