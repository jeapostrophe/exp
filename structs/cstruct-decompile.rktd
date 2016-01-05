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
              #hasheq((unsafe-set-cs-y!4.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-set-cs-y!4
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#11=#s((scope #(2 3 4) zo 0)
                                    11
                                    macro
                                    ((unsafe-set-cs-y!4
                                      (#11#
                                       .
                                       #12=(#13=#s((scope #(2 3 4) zo 0)
                                                   7
                                                   macro
                                                   ((^TYPE-tag
                                                     #14=(#13#
                                                          #4#
                                                          #15=#s((scope
                                                                  #(2 3 4)
                                                                  zo
                                                                  0)
                                                                 1
                                                                 module
                                                                 ((*in-array
                                                                   #16=(#15#
                                                                        .
                                                                        #17=(#s((scope
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
                                                                   #18=#s((module-binding
                                                                           binding
                                                                           0
                                                                           zo
                                                                           0)
                                                                          (insp0
                                                                           .
                                                                           #19={#%modidx
                                                                                #f
                                                                                #f})))
                                                                  (->
                                                                   #16#
                                                                   #18#)
                                                                  (:array-gen
                                                                   #16#
                                                                   #18#)
                                                                  (_?
                                                                   #16#
                                                                   #18#)
                                                                  (_array
                                                                   #16#
                                                                   #18#)
                                                                  (_array/list
                                                                   #16#
                                                                   #18#)
                                                                  (_array/vector
                                                                   #16#
                                                                   #18#)
                                                                  (_bitmask
                                                                   #16#
                                                                   #18#)
                                                                  (_bitmask*
                                                                   #16#
                                                                   #18#)
                                                                  (_box
                                                                   #16#
                                                                   #18#)
                                                                  (_byte
                                                                   #16#
                                                                   #18#)
                                                                  (_bytes*
                                                                   #16#
                                                                   #18#)
                                                                  (_bytes/eof
                                                                   #16#
                                                                   #18#)
                                                                  (_cpointer
                                                                   #16#
                                                                   #18#)
                                                                  (_cpointer/null
                                                                   #16#
                                                                   #18#)
                                                                  (_cprocedure
                                                                   #16#
                                                                   #18#)
                                                                  (_cprocedure*
                                                                   #16#
                                                                   #18#)
                                                                  (_enum
                                                                   #16#
                                                                   #18#)
                                                                  (_enum*
                                                                   #16#
                                                                   #18#)
                                                                  (_file
                                                                   #16#
                                                                   #18#)
                                                                  (_fun
                                                                   #16#
                                                                   #18#)
                                                                  (_gcable
                                                                   #16#
                                                                   #18#)
                                                                  (_int
                                                                   #16#
                                                                   #18#)
                                                                  (_intmax
                                                                   #16#
                                                                   #18#)
                                                                  (_intptr
                                                                   #16#
                                                                   #18#)
                                                                  (_list
                                                                   #16#
                                                                   #18#)
                                                                  (_list-struct
                                                                   #16#
                                                                   #18#)
                                                                  (_llong
                                                                   #16#
                                                                   #18#)
                                                                  (_long
                                                                   #16#
                                                                   #18#)
                                                                  (_or-null
                                                                   #16#
                                                                   #18#)
                                                                  (_ptr
                                                                   #16#
                                                                   #18#)
                                                                  (_ptrdiff
                                                                   #16#
                                                                   #18#)
                                                                  (_sbyte
                                                                   #16#
                                                                   #18#)
                                                                  (_short
                                                                   #16#
                                                                   #18#)
                                                                  (_sint
                                                                   #16#
                                                                   #18#)
                                                                  (_sint16
                                                                   #16#
                                                                   #18#)
                                                                  (_sint32
                                                                   #16#
                                                                   #18#)
                                                                  (_sint64
                                                                   #16#
                                                                   #18#)
                                                                  (_sint8
                                                                   #16#
                                                                   #18#)
                                                                  (_sintptr
                                                                   #16#
                                                                   #18#)
                                                                  (_size
                                                                   #16#
                                                                   #18#)
                                                                  (_sllong
                                                                   #16#
                                                                   #18#)
                                                                  (_slong
                                                                   #16#
                                                                   #18#)
                                                                  (_sshort
                                                                   #16#
                                                                   #18#)
                                                                  (_ssize
                                                                   #16#
                                                                   #18#)
                                                                  (_string
                                                                   #16#
                                                                   #18#)
                                                                  (_string*/latin-1
                                                                   #16#
                                                                   #18#)
                                                                  (_string*/locale
                                                                   #16#
                                                                   #18#)
                                                                  (_string*/utf-8
                                                                   #16#
                                                                   #18#)
                                                                  (_string/eof
                                                                   #16#
                                                                   #18#)
                                                                  (_string/latin-1
                                                                   #16#
                                                                   #18#)
                                                                  (_string/locale
                                                                   #16#
                                                                   #18#)
                                                                  (_string/utf-8
                                                                   #16#
                                                                   #18#)
                                                                  (_sword
                                                                   #16#
                                                                   #18#)
                                                                  (_ubyte
                                                                   #16#
                                                                   #18#)
                                                                  (_uint
                                                                   #16#
                                                                   #18#)
                                                                  (_uintmax
                                                                   #16#
                                                                   #18#)
                                                                  (_uintptr
                                                                   #16#
                                                                   #18#)
                                                                  (_ullong
                                                                   #16#
                                                                   #18#)
                                                                  (_ulong
                                                                   #16#
                                                                   #18#)
                                                                  (_union
                                                                   #16#
                                                                   #18#)
                                                                  (_ushort
                                                                   #16#
                                                                   #18#)
                                                                  (_uword
                                                                   #16#
                                                                   #18#)
                                                                  (_vector
                                                                   #16#
                                                                   #18#)
                                                                  (_word
                                                                   #16#
                                                                   #18#)
                                                                  (add-equality-property
                                                                   #16#
                                                                   #18#)
                                                                  (any-string-op
                                                                   #16#
                                                                   #18#)
                                                                  (array
                                                                   #16#
                                                                   #18#)
                                                                  (array-length
                                                                   #16#
                                                                   #18#)
                                                                  (array-ptr
                                                                   #16#
                                                                   #18#)
                                                                  (array-ref
                                                                   #16#
                                                                   #18#)
                                                                  (array-set!
                                                                   #16#
                                                                   #18#)
                                                                  (array-type
                                                                   #16#
                                                                   #18#)
                                                                  (array?
                                                                   #16#
                                                                   #18#)
                                                                  (cast
                                                                   #16#
                                                                   #18#)
                                                                  (cblock->list
                                                                   #16#
                                                                   #18#)
                                                                  (cblock->vector
                                                                   #16#
                                                                   #18#)
                                                                  (check-is-property
                                                                   #16#
                                                                   #18#)
                                                                  (compute-offsets
                                                                   #16#
                                                                   #18#)
                                                                  (cpointer-has-tag?
                                                                   #16#
                                                                   #18#)
                                                                  (cpointer-maker
                                                                   #16#
                                                                   #18#)
                                                                  (cpointer-push-tag!
                                                                   #16#
                                                                   #18#)
                                                                  (cstruct-info
                                                                   #16#
                                                                   #18#)
                                                                  (ctype->layout
                                                                   #16#
                                                                   #18#)
                                                                  (ctype-coretype
                                                                   #16#
                                                                   #18#)
                                                                  (default-_string-type
                                                                   #16#
                                                                   #18#)
                                                                  (define*
                                                                   #16#
                                                                   #18#)
                                                                  (define-c
                                                                   #16#
                                                                   #18#)
                                                                  (define-cpointer-type
                                                                   #16#
                                                                   #18#)
                                                                  (define-cstruct
                                                                   #16#
                                                                   #18#)
                                                                  (define-fun-syntax
                                                                   #16#
                                                                   #18#)
                                                                  (false-or-op
                                                                   #16#
                                                                   #18#)
                                                                  (ffi-get
                                                                   #16#
                                                                   #18#)
                                                                  (ffi-obj-ref
                                                                   #16#
                                                                   #18#)
                                                                  (ffi-objects-ref-table
                                                                   #16#
                                                                   #18#)
                                                                  (ffi-set!
                                                                   #16#
                                                                   #18#)
                                                                  (function-ptr
                                                                   #16#
                                                                   #18#)
                                                                  (get-ffi-lib
                                                                   #16#
                                                                   #18#)
                                                                  (get-ffi-lib-internal
                                                                   #16#
                                                                   #18#)
                                                                  (get-ffi-obj
                                                                   #16#
                                                                   #18#)
                                                                  (get-ffi-obj*
                                                                   #16#
                                                                   #18#)
                                                                  (get-ffi-obj-name
                                                                   #16#
                                                                   #18#)
                                                                  (get-lowlevel-object
                                                                   #16#
                                                                   #18#)
                                                                  (held-callbacks
                                                                   #16#
                                                                   #18#)
                                                                  (in-array
                                                                   #16#
                                                                   #18#)
                                                                  (killer-thread
                                                                   #16#
                                                                   #18#)
                                                                  (lib-suffix
                                                                   #16#
                                                                   #18#)
                                                                  (lib-suffix-re
                                                                   #16#
                                                                   #18#)
                                                                  (list->cblock
                                                                   #16#
                                                                   #18#)
                                                                  (make-array
                                                                   #16#
                                                                   #18#)
                                                                  (make-c-parameter
                                                                   #16#
                                                                   #18#)
                                                                  (make-union
                                                                   #16#
                                                                   #18#)
                                                                  (prim-synonyms
                                                                   #16#
                                                                   #18#)
                                                                  (register-finalizer
                                                                   #16#
                                                                   #18#)
                                                                  (set-ffi-obj!
                                                                   #16#
                                                                   #18#)
                                                                  (sizeof->3ints
                                                                   #16#
                                                                   #18#)
                                                                  (string-type->string/eof-type
                                                                   #16#
                                                                   #18#)
                                                                  (struct:array
                                                                   #16#
                                                                   #18#)
                                                                  (struct:union
                                                                   #16#
                                                                   #18#)
                                                                  (suffix-before-version?
                                                                   #16#
                                                                   #18#)
                                                                  (union
                                                                   #16#
                                                                   #18#)
                                                                  (union-ptr
                                                                   #16#
                                                                   #18#)
                                                                  (union-ref
                                                                   #16#
                                                                   #18#)
                                                                  (union-set!
                                                                   #16#
                                                                   #18#)
                                                                  (union-types
                                                                   #16#
                                                                   #18#)
                                                                  (union?
                                                                   #16#
                                                                   #18#)
                                                                  (vector->cblock
                                                                   #16#
                                                                   #18#)
                                                                  (version-sep
                                                                   #16#
                                                                   #18#))
                                                                 ((#16#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #7#
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#16#
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
                                                                  (#16#
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
                                                                  (#16#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #9#
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f))
                                                                  (#16#
                                                                   #s((all-from-module
                                                                       zo
                                                                       0)
                                                                      #20={#%modidx
                                                                           racket/private/for
                                                                           #f}
                                                                      0
                                                                      0
                                                                      insp0
                                                                      ()
                                                                      #f)))
                                                                 #21=#s((multi-scope
                                                                         #(2)
                                                                         zo
                                                                         0)
                                                                        64
                                                                        unsafe
                                                                        ((0
                                                                          #15#)
                                                                         (1
                                                                          #22=#s((scope
                                                                                  #(2
                                                                                    3
                                                                                    4)
                                                                                  zo
                                                                                  0)
                                                                                 2
                                                                                 module
                                                                                 ((_fun-keywords
                                                                                   #23=(#22#
                                                                                        .
                                                                                        #17#)
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       _fun-keywords
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       _fun-keywords)))
                                                                                  (custom-type->keys
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       custom-type->keys
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       custom-type->keys)))
                                                                                  (disarm
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       disarm
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       disarm)))
                                                                                  (expand-fun-syntax/fun
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       expand-fun-syntax/fun
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       expand-fun-syntax/fun)))
                                                                                  (expand-fun-syntax/normal
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       expand-fun-syntax/normal
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       expand-fun-syntax/normal)))
                                                                                  (fun-syntax-name
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       fun-syntax-name
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax-name)))
                                                                                  (fun-syntax-proc
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       fun-syntax-proc
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax-proc)))
                                                                                  (fun-syntax?
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       fun-syntax?
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       fun-syntax?)))
                                                                                  (id=?
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       id=?
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       id=?)))
                                                                                  (make-fun-syntax
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       make-fun-syntax
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       make-fun-syntax)))
                                                                                  (orig-inspector
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       orig-inspector
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       orig-inspector)))
                                                                                  (split-by
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       split-by
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       split-by)))
                                                                                  (with-renamer
                                                                                   #23#
                                                                                   #s((module-binding
                                                                                       binding
                                                                                       0
                                                                                       zo
                                                                                       0)
                                                                                      (insp0
                                                                                       #19#
                                                                                       1
                                                                                       with-renamer
                                                                                       (#19#
                                                                                        .
                                                                                        1)
                                                                                       .
                                                                                       with-renamer))))
                                                                                 ((#23#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      1
                                                                                      0
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#23#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #20#
                                                                                      1
                                                                                      0
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#23#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#23#
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
                                                                                  (#23#
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
                                                                                  (#23#
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      {#%modidx
                                                                                       racket/syntax
                                                                                       #f}
                                                                                      0
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f))
                                                                                  (#23#
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
                                                                                 #21#))
                                                                         (2
                                                                          #24=#s((scope
                                                                                  #(2
                                                                                    3
                                                                                    4)
                                                                                  zo
                                                                                  0)
                                                                                 3
                                                                                 module
                                                                                 ()
                                                                                 (((#24#
                                                                                    .
                                                                                    #17#)
                                                                                   #s((all-from-module
                                                                                       zo
                                                                                       0)
                                                                                      #7#
                                                                                      1
                                                                                      1
                                                                                      insp0
                                                                                      ()
                                                                                      #f)))
                                                                                 #21#)))))
                                                          .
                                                          #17#)
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                                     #14#
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
                                         (insp0 #0# . unsafe-set-cs-y!4.0))))
                                    ()
                                    #f)
                             .
                             #25=(#13#))
                            ((#3# 0)))}))
                      (unsafe-cs-y
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-y
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           24
                           10
                           549
                           11)
                         #1#
                         #26=#s((wrap zo 0)
                                (#s((module-shift zo 0)
                                    {#%modidx #f #f}
                                    #0#
                                    #f
                                    #f))
                                #2#
                                ((#3# 0)))}))
                      (cs
                       .
                       (#%decode-syntax
                        {wrap
                         cs
                         #27=#(struct:srcloc
                               #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                               6
                               17
                               107
                               3)
                         #1#
                         #26#}))
                      (cs->list
                       .
                       (#%decode-syntax {wrap cs->list #27# #1# #26#}))
                      (cs->list*
                       .
                       (#%decode-syntax {wrap cs->list* #27# #1# #26#}))
                      (wrap-cs-type
                       .
                       (#%decode-syntax {wrap wrap-cs-type #27# #1# #26#}))
                      (cs-tag . (#%decode-syntax {wrap cs-tag #27# #1# #26#}))
                      (cs-x . (#%decode-syntax {wrap cs-x #27# #1# #26#}))
                      (cs-x-type
                       .
                       (#%decode-syntax {wrap cs-x-type #27# #1# #26#}))
                      (^TYPE-tag.0
                       .
                       (#%decode-syntax
                        {wrap
                         ^TYPE-tag
                         #28=#(struct:srcloc
                               ".../ffi/unsafe.rkt"
                               1553
                               35
                               69135
                               6)
                         #1#
                         #29=#s((wrap zo 0)
                                (#s((module-shift zo 0) #19# #8# insp0 insp0)
                                 #s((module-shift zo 0)
                                    {#%modidx #f #f}
                                    #19#
                                    #f
                                    #f))
                                (#13# . #17#)
                                ((#3# 0) (#21# 0)))}))
                      (cs-y . (#%decode-syntax {wrap cs-y #27# #1# #26#}))
                      (^TYPE?.0
                       .
                       (#%decode-syntax {wrap ^TYPE? #28# #1# #29#}))
                      (_^TYPE.0
                       .
                       (#%decode-syntax {wrap _^TYPE #28# #1# #29#}))
                      (cs-y-type
                       .
                       (#%decode-syntax {wrap cs-y-type #27# #1# #26#}))
                      (_^TYPE/null.0
                       .
                       (#%decode-syntax {wrap _^TYPE/null #28# #1# #29#}))
                      (cs? . (#%decode-syntax {wrap cs? #27# #1# #26#}))
                      (alignment-v.0
                       .
                       (#%decode-syntax
                        {wrap
                         alignment-v
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1560 21 69522 11)
                         #1#
                         #29#}))
                      (list*->cs
                       .
                       (#%decode-syntax {wrap list*->cs #27# #1# #26#}))
                      (all-offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1575 39 70358 11)
                         #1#
                         #29#}))
                      (all-tags.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-tags
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1563 21 69717 8)
                         #1#
                         #29#}))
                      (list->cs
                       .
                       (#%decode-syntax {wrap list->cs #27# #1# #26#}))
                      (all-types.0
                       .
                       (#%decode-syntax
                        {wrap
                         all-types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1575 29 70348 9)
                         #1#
                         #29#}))
                      (make-cs
                       .
                       (#%decode-syntax {wrap make-cs #27# #1# #26#}))
                      (cs-x-offset5.0
                       .
                       (#%decode-syntax
                        {wrap
                         cs-x-offset5
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#30=#s((scope #(2 3 4) zo 0)
                                    12
                                    macro
                                    ((cs-x-offset5
                                      (#30# . #12#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . cs-x-offset5.0))))
                                    ()
                                    #f)
                             .
                             #25#)
                            ((#3# 0)))}))
                      (cs-y-offset6.0
                       .
                       (#%decode-syntax
                        {wrap
                         cs-y-offset6
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#31=#s((scope #(2 3 4) zo 0)
                                    13
                                    macro
                                    ((cs-y-offset6
                                      (#31# . #12#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . cs-y-offset6.0))))
                                    ()
                                    #f)
                             .
                             #25#)
                            ((#3# 0)))}))
                      (set-cs-x!
                       .
                       (#%decode-syntax {wrap set-cs-x! #27# #1# #26#}))
                      (list*->super.0
                       .
                       (#%decode-syntax
                        {wrap
                         list*->super
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1549 56 68889 12)
                         #1#
                         #29#}))
                      (set-cs-y!
                       .
                       (#%decode-syntax {wrap set-cs-y! #27# #1# #26#}))
                      (offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1561 21 69565 7)
                         #1#
                         #29#}))
                      (struct:cpointer:super.0
                       .
                       (#%decode-syntax
                        {wrap
                         struct:cpointer:super
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1550 43 68944 21)
                         #1#
                         #29#}))
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
                         #26#}))
                      (super->list*.0
                       .
                       (#%decode-syntax
                        {wrap
                         super->list*
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1549 43 68876 12)
                         #1#
                         #29#}))
                      (super-offsets.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-offsets
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 66 68820 13)
                         #1#
                         #29#}))
                      (super-pointer.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-pointer
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 29 68783 13)
                         #1#
                         #29#}))
                      (super-tags.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-tags
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 43 68797 10)
                         #1#
                         #29#}))
                      (super-types.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1548 54 68808 11)
                         #1#
                         #29#}))
                      (super-wrap-type-type.0
                       .
                       (#%decode-syntax
                        {wrap
                         super-wrap-type-type
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1550 65 68966 20)
                         #1#
                         #29#}))
                      (_cs . (#%decode-syntax {wrap _cs #27# #1# #26#}))
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
                         #26#}))
                      (types.0
                       .
                       (#%decode-syntax
                        {wrap
                         types
                         #(struct:srcloc ".../ffi/unsafe.rkt" 1559 21 69478 5)
                         #1#
                         #29#}))
                      (_cs-pointer
                       .
                       (#%decode-syntax {wrap _cs-pointer #27# #1# #26#}))
                      (test-unsafe-fun
                       .
                       (#%decode-syntax
                        {wrap
                         test-unsafe-fun
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           26
                           10
                           605
                           15)
                         #1#
                         #26#}))
                      (unsafe-cs-x1.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-x1
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#32=#s((scope #(2 3 4) zo 0)
                                    8
                                    macro
                                    ((unsafe-cs-x1
                                      (#32# . #12#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-cs-x1.0))))
                                    ()
                                    #f)
                             .
                             #25#)
                            ((#3# 0)))}))
                      (_cs-pointer/null
                       .
                       (#%decode-syntax {wrap _cs-pointer/null #27# #1# #26#}))
                      (unsafe-cs-y2.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-y2
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#33=#s((scope #(2 3 4) zo 0)
                                    9
                                    macro
                                    ((unsafe-cs-y2
                                      (#33# . #12#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-cs-y2.0))))
                                    ()
                                    #f)
                             .
                             #25#)
                            ((#3# 0)))}))
                      (unsafe-cs-x
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-cs-x
                         #(struct:srcloc
                           #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                           22
                           10
                           493
                           11)
                         #1#
                         #26#}))
                      (unsafe-set-cs-x!3.0
                       .
                       (#%decode-syntax
                        {wrap
                         unsafe-set-cs-x!3
                         #1#
                         #s((wrap zo 0)
                            ()
                            (#34=#s((scope #(2 3 4) zo 0)
                                    10
                                    macro
                                    ((unsafe-set-cs-x!3
                                      (#34# . #12#)
                                      #s((module-binding binding 0 zo 0)
                                         (insp0 #0# . unsafe-set-cs-x!3.0))))
                                    ()
                                    #f)
                             .
                             #25#)
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
         (define stx31 (#%decode-syntax {wrap make-cs #27# #1# #26#}))
         (define stx32 (#%decode-syntax {wrap cs? #27# #1# #26#}))
         (define stx33 (#%decode-syntax {wrap cs-x #27# #1# #26#}))
         (define stx34 (#%decode-syntax {wrap cs-y #27# #1# #26#}))
         (define stx35 (#%decode-syntax {wrap set-cs-x! #27# #1# #26#}))
         (define stx36 (#%decode-syntax {wrap set-cs-y! #27# #1# #26#}))
         (|_make-struct-info@(lib "racket/private/struct-info.rkt")|
          (lambda ()
            '...s/ffi/unsafe.rkt:1541:15
            '(flags: preserves-marks single-result)
            '(captures:
              (val/ref #%globals)
              (|_alt-reverse:f@(lib "racket/private/reverse.rkt")| #%syntax))
            (list
             '#f
             stx31
             stx32
             (|_alt-reverse:f@(lib "racket/private/reverse.rkt")|
              (list stx33 stx34))
             (|_alt-reverse:f@(lib "racket/private/reverse.rkt")|
              (list stx35 stx36))
             '#t))))))
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
       ...s/ffi/unsafe.rkt:1495:2723
       (lambda ()
         '...s/ffi/unsafe.rkt:1495:27
         (values '#f '() '#f '#f '#f '#f '#f values)))))
    (define-values (_^TYPE-tag.0) (gensym '^TYPE))
    (define-values
     (__^TYPE.0)
     (|__cpointer:f@(lib "ffi/unsafe.rkt")|
      _^TYPE-tag.0
      (#%checked _super-pointer.0)
      '#f
      '#f))
    (define-values
     (__^TYPE/null.0)
     (|__cpointer/null:f@(lib "ffi/unsafe.rkt")|
      _^TYPE-tag.0
      (#%checked _super-pointer.0)
      '#f
      '#f))
    (define-values
     (_^TYPE?.0)
     (lambda (arg0-69)
       '^TYPE?
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0 |_memq@(lib "racket/private/member.rkt")|))
       (if (cpointer? arg0-69)
         (let ((local71 (cpointer-tag (#%sfs-clear arg0-69))))
           (if (pair? local71)
             (if (null? (unsafe-cdr local71))
               (eq? _^TYPE-tag.0 (unsafe-car local71))
               (if (|_memq@(lib "racket/private/member.rkt")|
                    _^TYPE-tag.0
                    (#%sfs-clear local71))
                 '#t
                 '#f))
             (eq? _^TYPE-tag.0 local71)))
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
    (define-values (_cs-x-offset5.0 _cs-y-offset6.0) (apply values _offsets.0))
    (define-values (_all-tags.0) (cons _^TYPE-tag.0 (#%checked _super-tags.0)))
    (define-values
     (__cs)
     (let ((local98 (make-cstruct-type _types.0 '#f '#f)))
       (let ((local102
              (|__cpointer:f@(lib "ffi/unsafe.rkt")| _^TYPE-tag.0 local98)))
         (let ((local105 (ctype-c->scheme local102)))
           (_wrap-cs-type
            (make-ctype
             (#%sfs-clear local98)
             (ctype-scheme->c (#%sfs-clear local102))
             (begin0
               (lambda (arg0-112)
                 '...s/ffi/unsafe.rkt:1572:29
                 '(flags: preserves-marks single-result)
                 '(captures:
                   (val/ref local105)
                   (val/ref #%modvars)
                   (_all-tags.0))
                 (begin
                   (if arg0-112
                     (begin
                       (#%sfs-clear local105)
                       (set-cpointer-tag! arg0-112 _all-tags.0))
                     ((#%sfs-clear local105) '#f))
                   arg0-112))
               (#%sfs-clear local105))))))))
    (define-values (_all-types.0 _all-offsets.0) (values _types.0 _offsets.0))
    (define-values
     (_unsafe-cs-x1.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-118)
         'unsafe-cs-x1
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-x-offset5.0))
         (ptr-ref arg0-118 _double 'abs (#%checked _cs-x-offset5.0)))
       (lambda (arg0-123)
         'unsafe-cs-x1
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-x-offset5.0))
         (ptr-ref
          (#%sfs-clear arg0-123)
          _double
          'abs
          (#%checked _cs-x-offset5.0)))))
    (define-values
     (_cs-x)
     (lambda (arg0-128)
       'cs-x
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _cs-x-offset5.0))
       (begin
         (if (if (cpointer? arg0-128)
               (let ((local130 (cpointer-tag arg0-128)))
                 (if (pair? local130)
                   (if (null? (unsafe-cdr local130))
                     (eq? _^TYPE-tag.0 (unsafe-car local130))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local130)))
                   (eq? _^TYPE-tag.0 local130)))
               '#f)
           '#<void>
           (raise-argument-error 'cs-x '"cs?" arg0-128))
         (ptr-ref
          (#%sfs-clear arg0-128)
          _double
          'abs
          (#%checked _cs-x-offset5.0)))))
    (define-values
     (_unsafe-cs-y2.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-149)
         'unsafe-cs-y2
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-y-offset6.0))
         (ptr-ref arg0-149 _double 'abs _cs-y-offset6.0))
       (lambda (arg0-154)
         'unsafe-cs-y2
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-y-offset6.0))
         (ptr-ref (#%sfs-clear arg0-154) _double 'abs _cs-y-offset6.0))))
    (define-values
     (_cs-y)
     (lambda (arg0-159)
       'cs-y
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _cs-y-offset6.0))
       (begin
         (if (if (cpointer? arg0-159)
               (let ((local161 (cpointer-tag arg0-159)))
                 (if (pair? local161)
                   (if (null? (unsafe-cdr local161))
                     (eq? _^TYPE-tag.0 (unsafe-car local161))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local161)))
                   (eq? _^TYPE-tag.0 local161)))
               '#f)
           '#<void>
           (raise-argument-error 'cs-y '"cs?" arg0-159))
         (ptr-ref (#%sfs-clear arg0-159) _double 'abs _cs-y-offset6.0))))
    (define-values
     (_unsafe-set-cs-x!3.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-180 arg1-181)
         'unsafe-set-cs-x!3
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-x-offset5.0))
         (ptr-set! arg0-180 _double 'abs (#%checked _cs-x-offset5.0) arg1-181))
       (lambda (arg0-187 arg1-188)
         'unsafe-set-cs-x!3
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-x-offset5.0))
         (ptr-set!
          (#%sfs-clear arg0-187)
          _double
          'abs
          (#%checked _cs-x-offset5.0)
          (#%sfs-clear arg1-188)))))
    (define-values
     (_set-cs-x!)
     (lambda (arg0-194 arg1-195)
       'set-cs-x!
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _cs-x-offset5.0))
       (begin
         (if (if (cpointer? arg0-194)
               (let ((local197 (cpointer-tag arg0-194)))
                 (if (pair? local197)
                   (if (null? (unsafe-cdr local197))
                     (eq? _^TYPE-tag.0 (unsafe-car local197))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local197)))
                   (eq? _^TYPE-tag.0 local197)))
               '#f)
           '#<void>
           (raise-argument-error 'set-cs-x! '"cs?" '0 arg0-194 arg1-195))
         (ptr-set!
          (#%sfs-clear arg0-194)
          _double
          'abs
          (#%checked _cs-x-offset5.0)
          (#%sfs-clear arg1-195)))))
    (define-values
     (_unsafe-set-cs-y!4.0)
     (begin
       '%%inline-variant%%
       (lambda (arg0-219 arg1-220)
         'unsafe-set-cs-y!4
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-y-offset6.0))
         (ptr-set! arg0-219 _double 'abs _cs-y-offset6.0 arg1-220))
       (lambda (arg0-226 arg1-227)
         'unsafe-set-cs-y!4
         '(flags: preserves-marks single-result)
         '(captures: (val/ref #%modvars) (_cs-y-offset6.0))
         (ptr-set!
          (#%sfs-clear arg0-226)
          _double
          'abs
          _cs-y-offset6.0
          (#%sfs-clear arg1-227)))))
    (define-values
     (_set-cs-y!)
     (lambda (arg0-233 arg1-234)
       'set-cs-y!
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _cs-y-offset6.0))
       (begin
         (if (if (cpointer? arg0-233)
               (let ((local236 (cpointer-tag arg0-233)))
                 (if (pair? local236)
                   (if (null? (unsafe-cdr local236))
                     (eq? _^TYPE-tag.0 (unsafe-car local236))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local236)))
                   (eq? _^TYPE-tag.0 local236)))
               '#f)
           '#<void>
           (raise-argument-error 'set-cs-y! '"cs?" '0 arg0-233 arg1-234))
         (ptr-set!
          (#%sfs-clear arg0-233)
          _double
          'abs
          _cs-y-offset6.0
          (#%sfs-clear arg1-234)))))
    (define-values
     (_make-cs)
     (lambda (arg0-258 arg1-259)
       'make-cs
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_cs-x-offset5.0 _cs-y-offset6.0 _all-tags.0 __cs))
       (let ((local260 (malloc __cs 'atomic)))
         (begin
           (set-cpointer-tag! local260 _all-tags.0)
           (ptr-set!
            local260
            _double
            'abs
            (#%checked _cs-x-offset5.0)
            (#%sfs-clear arg0-258))
           (ptr-set!
            local260
            _double
            'abs
            _cs-y-offset6.0
            (#%sfs-clear arg1-259))
           local260))))
    (define-values
     (_list->cs)
     (begin
       '%%inline-variant%%
       (lambda (arg0-275)
         'list->cs
         '(captures: (val/ref #%modvars) (_make-cs))
         (apply _make-cs arg0-275))
       (lambda (arg0-278)
         'list->cs
         '(captures: (val/ref #%modvars) (_make-cs))
         (apply _make-cs (#%sfs-clear arg0-278)))))
    (define-values
     (_list*->cs)
     (lambda (arg0-281)
       'list*->cs
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
          _^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _all-tags.0
          __cs
          _all-types.0
          _all-offsets.0))
       (if (if (cpointer? arg0-281)
             (let ((local283 (cpointer-tag arg0-281)))
               (if (pair? local283)
                 (if (null? (unsafe-cdr local283))
                   (eq? _^TYPE-tag.0 (unsafe-car local283))
                   (|_memq@(lib "racket/private/member.rkt")|
                    _^TYPE-tag.0
                    (#%sfs-clear local283)))
                 (eq? _^TYPE-tag.0 local283)))
             '#f)
         arg0-281
         (if (= (length arg0-281) (length (#%checked _all-types.0)))
           (let ((local299 (malloc __cs 'atomic)))
             (begin
               (set-cpointer-tag! local299 _all-tags.0)
               (let ((...s/ffi/unsafe.rkt:1626:20304
                      (lambda (arg0-305 arg1-306 arg2-307)
                        '...s/ffi/unsafe.rkt:1626:20
                        '(flags: preserves-marks single-result)
                        '(captures:
                          (val/ref local299)
                          (val/ref #%modvars)
                          (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|))
                        (let ((localv308 ?)
                              (localv309 ?)
                              (localv310 ?)
                              (localv311 ?)
                              (localv312 ?)
                              (localv313 ?)
                              (localv314 ?)
                              (localv315 ?))
                          (begin
                            (set!-values (localv308
                                          localv309
                                          localv310
                                          localv311
                                          localv312
                                          localv313
                                          localv314
                                          localv315)
                              (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                               arg0-305
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
                              (#%sfs-clear localv315)
                              (#%sfs-clear localv314)
                              (#%sfs-clear localv312)
                              (#%sfs-clear localv311)
                              (#%sfs-clear localv310)
                              (#%sfs-clear localv309)
                              (#%sfs-clear localv308)
                              (ptr-set!
                               (#%sfs-clear local299)
                               (#%sfs-clear arg0-305)
                               'abs
                               (#%sfs-clear arg1-306)
                               (if localv313
                                 ((#%sfs-clear localv313)
                                  (#%sfs-clear arg2-307))
                                 (begin
                                   (#%sfs-clear localv313)
                                   (#%sfs-clear arg2-307))))))))))
                 (for-each
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1626:20304)
                  (#%checked _all-types.0)
                  _all-offsets.0
                  (#%sfs-clear arg0-281)))
               local299))
           (error
            '_cs
            '"expecting ~s values, got ~s: ~e"
            (length (#%checked _all-types.0))
            (length arg0-281)
            (#%sfs-clear arg0-281))))))
    (define-values
     (_cs->list)
     (lambda (arg0-343)
       'cs->list
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _all-types.0
          _all-offsets.0))
       (begin
         (if (if (cpointer? arg0-343)
               (let ((local345 (cpointer-tag arg0-343)))
                 (if (pair? local345)
                   (if (null? (unsafe-cdr local345))
                     (eq? _^TYPE-tag.0 (unsafe-car local345))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local345)))
                   (eq? _^TYPE-tag.0 local345)))
               '#f)
           '#<void>
           (raise-argument-error 'TYPE-list '"cs?" arg0-343))
         (let ((...s/ffi/unsafe.rkt:1641:19360
                (lambda (arg0-361 arg1-362)
                  '...s/ffi/unsafe.rkt:1641:19
                  '(flags: preserves-marks single-result)
                  '(captures: (val/ref arg0-343))
                  (ptr-ref
                   (#%sfs-clear arg0-343)
                   (#%sfs-clear arg0-361)
                   'abs
                   (#%sfs-clear arg1-362)))))
           (let ((local367 (#%checked _all-types.0)))
             (if (if (list? local367)
                   (if (list? _all-offsets.0)
                     (= (length local367) (length _all-offsets.0))
                     '#f)
                   '#f)
               ((#%closed
                 loop18
                 (lambda (arg0-377 arg1-378 arg2-379)
                   'loop
                   '(flags: preserves-marks single-result)
                   (if (null? arg1-378)
                     '()
                     (cons
                      (ptr-ref arg0-377 (car arg1-378) 'abs (car arg2-379))
                      (let ((local389 (unsafe-cdr (#%sfs-clear arg1-378))))
                        (let ((local391 (unsafe-cdr (#%sfs-clear arg2-379))))
                          (if (null? local389)
                            '()
                            (cons
                             (ptr-ref
                              arg0-377
                              (car local389)
                              'abs
                              (car local391))
                             (let ((local402
                                    (unsafe-cdr (#%sfs-clear local389))))
                               (let ((local404
                                      (unsafe-cdr (#%sfs-clear local391))))
                                 (if (null? local402)
                                   '()
                                   (cons
                                    (ptr-ref
                                     arg0-377
                                     (car local402)
                                     'abs
                                     (car local404))
                                    (loop18
                                     (#%sfs-clear arg0-377)
                                     (unsafe-cdr (#%sfs-clear local402))
                                     (unsafe-cdr
                                      (#%sfs-clear local404)))))))))))))))
                arg0-343
                local367
                _all-offsets.0)
               (begin
                 (#%sfs-clear arg0-343)
                 (map
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1641:19360)
                  (#%sfs-clear local367)
                  _all-offsets.0))))))))
    (define-values
     (lift28)
     (lambda (arg0-423 arg1-424 arg2-425 arg3-426)
       'loop
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")| lift28))
       (if (null? arg2-425)
         '()
         (cons
          (let ((local430 (car arg2-425)))
            (let ((localv432 ?)
                  (localv433 ?)
                  (localv434 ?)
                  (localv435 ?)
                  (localv436 ?)
                  (localv437 ?)
                  (localv438 ?)
                  (localv439 ?)
                  (localv440 ?))
              (begin
                (set!-values (localv432)
                  (ptr-ref arg1-424 local430 'abs (car arg3-426)))
                (begin
                  (set!-values (localv433
                                localv434
                                localv435
                                localv436
                                localv437
                                localv438
                                localv439
                                localv440)
                    (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                     (#%sfs-clear local430)
                     (#%closed
                      ...s/ffi/unsafe.rkt:1652:2819
                      (lambda ()
                        '...s/ffi/unsafe.rkt:1652:28
                        (values '#f '() '#f '#f '#f '#f '#f values)))))
                  (begin
                    (#%sfs-clear localv440)
                    (#%sfs-clear localv439)
                    (#%sfs-clear localv438)
                    (#%sfs-clear localv436)
                    (#%sfs-clear localv435)
                    (#%sfs-clear localv434)
                    (#%sfs-clear localv433)
                    (if localv437
                      ((#%sfs-clear localv437) (#%sfs-clear localv432))
                      localv432))))))
          (let ((local457 (unsafe-cdr (#%sfs-clear arg2-425))))
            (let ((local459 (unsafe-cdr (#%sfs-clear arg3-426))))
              (if (null? local457)
                '()
                (cons
                 (let ((local464 (car local457)))
                   (let ((localv466 ?)
                         (localv467 ?)
                         (localv468 ?)
                         (localv469 ?)
                         (localv470 ?)
                         (localv471 ?)
                         (localv472 ?)
                         (localv473 ?)
                         (localv474 ?))
                     (begin
                       (set!-values (localv466)
                         (ptr-ref arg1-424 local464 'abs (car local459)))
                       (begin
                         (set!-values (localv467
                                       localv468
                                       localv469
                                       localv470
                                       localv471
                                       localv472
                                       localv473
                                       localv474)
                           (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                            (#%sfs-clear local464)
                            (#%closed
                             ...s/ffi/unsafe.rkt:1652:2820
                             (lambda ()
                               '...s/ffi/unsafe.rkt:1652:28
                               (values '#f '() '#f '#f '#f '#f '#f values)))))
                         (begin
                           (#%sfs-clear localv474)
                           (#%sfs-clear localv473)
                           (#%sfs-clear localv472)
                           (#%sfs-clear localv470)
                           (#%sfs-clear localv469)
                           (#%sfs-clear localv468)
                           (#%sfs-clear localv467)
                           (if localv471
                             ((#%sfs-clear localv471) (#%sfs-clear localv466))
                             localv466))))))
                 (let ((local491 (unsafe-cdr (#%sfs-clear local457))))
                   (let ((local493 (unsafe-cdr (#%sfs-clear local459))))
                     (if (null? local491)
                       '()
                       (cons
                        (arg0-423 (car local491) (car local493))
                        (lift28
                         (#%sfs-clear arg0-423)
                         (#%sfs-clear arg1-424)
                         (unsafe-cdr (#%sfs-clear local491))
                         (unsafe-cdr (#%sfs-clear local493)))))))))))))))
    (define-values
     (_cs->list*)
     (lambda (arg0-508)
       'cs->list*
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
          _^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _all-types.0
          _all-offsets.0
          lift28))
       (begin
         (if (if (cpointer? arg0-508)
               (let ((local510 (cpointer-tag arg0-508)))
                 (if (pair? local510)
                   (if (null? (unsafe-cdr local510))
                     (eq? _^TYPE-tag.0 (unsafe-car local510))
                     (|_memq@(lib "racket/private/member.rkt")|
                      _^TYPE-tag.0
                      (#%sfs-clear local510)))
                   (eq? _^TYPE-tag.0 local510)))
               '#f)
           '#<void>
           (raise-argument-error 'TYPE-list '"cs?" arg0-508))
         (let ((...s/ffi/unsafe.rkt:1646:19525
                (lambda (arg0-526 arg1-527)
                  '...s/ffi/unsafe.rkt:1646:19
                  '(captures:
                    (val/ref arg0-508)
                    (val/ref #%modvars)
                    (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|))
                  (let ((localv528 ?)
                        (localv529 ?)
                        (localv530 ?)
                        (localv531 ?)
                        (localv532 ?)
                        (localv533 ?)
                        (localv534 ?)
                        (localv535 ?)
                        (localv536 ?))
                    (begin
                      (set!-values (localv528)
                        (ptr-ref
                         (#%sfs-clear arg0-508)
                         arg0-526
                         'abs
                         (#%sfs-clear arg1-527)))
                      (begin
                        (set!-values (localv529
                                      localv530
                                      localv531
                                      localv532
                                      localv533
                                      localv534
                                      localv535
                                      localv536)
                          (|_cstruct-info:f@(lib "ffi/unsafe.rkt")|
                           (#%sfs-clear arg0-526)
                           (#%closed
                            ...s/ffi/unsafe.rkt:1652:2821
                            (lambda ()
                              '...s/ffi/unsafe.rkt:1652:28
                              (values '#f '() '#f '#f '#f '#f '#f values)))))
                        (begin
                          (#%sfs-clear localv536)
                          (#%sfs-clear localv535)
                          (#%sfs-clear localv534)
                          (#%sfs-clear localv532)
                          (#%sfs-clear localv531)
                          (#%sfs-clear localv530)
                          (#%sfs-clear localv529)
                          (if localv533
                            ((#%sfs-clear localv533) (#%sfs-clear localv528))
                            localv528))))))))
           (let ((local552 (#%checked _all-types.0)))
             (if (if (list? local552)
                   (if (list? _all-offsets.0)
                     (= (length local552) (length _all-offsets.0))
                     '#f)
                   '#f)
               (lift28
                ...s/ffi/unsafe.rkt:1646:19525
                arg0-508
                local552
                _all-offsets.0)
               (begin
                 (#%sfs-clear arg0-508)
                 (map
                  (#%sfs-clear ...s/ffi/unsafe.rkt:1646:19525)
                  (#%sfs-clear local552)
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
    (define-values (_cs-tag) _^TYPE-tag.0)
    (define-values (_N) '180000)
    (define-values
     (lift29)
     (lambda (arg0-576 argflonum1-577 arg2-578)
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
         (_^TYPE-tag.0
          |_memq@(lib "racket/private/member.rkt")|
          _cs-x-offset5.0
          _cs-y-offset6.0
          _cs-x
          _cs-y
          lift29))
       (if (< arg2-578 '180000)
         (let ((flonum581
                (fl+
                 argflonum1-577
                 (fl+
                  (begin
                    (if (if (cpointer? arg0-576)
                          (let ((local587 (cpointer-tag arg0-576)))
                            (if (pair? local587)
                              (if (null? (unsafe-cdr local587))
                                (eq? _^TYPE-tag.0 (unsafe-car local587))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 _^TYPE-tag.0
                                 (#%sfs-clear local587)))
                              (eq? _^TYPE-tag.0 local587)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-x '"cs?" arg0-576))
                    (ptr-ref
                     arg0-576
                     _double
                     'abs
                     (#%checked _cs-x-offset5.0)))
                  (begin
                    (if (if (cpointer? arg0-576)
                          (let ((local607 (cpointer-tag arg0-576)))
                            (if (pair? local607)
                              (if (null? (unsafe-cdr local607))
                                (eq? _^TYPE-tag.0 (unsafe-car local607))
                                (|_memq@(lib "racket/private/member.rkt")|
                                 _^TYPE-tag.0
                                 (#%sfs-clear local607)))
                              (eq? _^TYPE-tag.0 local607)))
                          '#f)
                      '#<void>
                      (raise-argument-error 'cs-y '"cs?" arg0-576))
                    (ptr-ref arg0-576 _double 'abs _cs-y-offset6.0))))))
           (let ((local626 (+ (#%sfs-clear arg2-578) '1)))
             (if (< local626 '180000)
               (let ((flonum631
                      (fl+ flonum581 (fl+ (_cs-x arg0-576) (_cs-y arg0-576)))))
                 (let ((local638 (+ (#%sfs-clear local626) '1)))
                   (if (< local638 '180000)
                     (let ((flonum643
                            (fl+
                             flonum631
                             (fl+ (_cs-x arg0-576) (_cs-y arg0-576)))))
                       (let ((local650 (+ (#%sfs-clear local638) '1)))
                         (if (< local650 '180000)
                           (lift29
                            arg0-576
                            (fl+
                             flonum643
                             (fl+
                              (_cs-x arg0-576)
                              (_cs-y (#%sfs-clear arg0-576))))
                            (+ local650 '1))
                           flonum643)))
                     flonum631)))
               flonum581)))
         argflonum1-577)))
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
         (_cs-x-offset5.0 _cs-y-offset6.0 _all-tags.0 __cs lift29))
       (let ((local666
              (let ((local667 (malloc __cs 'atomic)))
                (begin
                  (set-cpointer-tag! local667 _all-tags.0)
                  (ptr-set!
                   local667
                   _double
                   'abs
                   (#%checked _cs-x-offset5.0)
                   '1.0)
                  (ptr-set! local667 _double 'abs _cs-y-offset6.0 '2.0)
                  local667))))
         (lift29 local666 '0.0 '0))))
    (define-values
     (_unsafe-cs-x)
     (begin
       '%%inline-variant%%
       (#%closed
        unsafe-cs-x25
        (lambda (arg0-685)
          '#(unsafe-cs-x
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             22
             0
             484
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref arg0-685 _double 'abs '0)))
       (#%closed
        unsafe-cs-x24
        (lambda (arg0-690)
          '#(unsafe-cs-x
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             22
             0
             484
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref (#%sfs-clear arg0-690) _double 'abs '0)))))
    (define-values
     (_unsafe-cs-y)
     (begin
       '%%inline-variant%%
       (#%closed
        unsafe-cs-y27
        (lambda (arg0-695)
          '#(unsafe-cs-y
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             24
             0
             540
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref arg0-695 _double 'abs '8)))
       (#%closed
        unsafe-cs-y26
        (lambda (arg0-700)
          '#(unsafe-cs-y
             #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
             24
             0
             540
             55
             #f)
          '(flags: preserves-marks single-result)
          (ptr-ref (#%sfs-clear arg0-700) _double 'abs '8)))))
    (define-values
     (_test-unsafe-fun)
     (lambda ()
       '#(test-unsafe-fun
          #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
          26
          0
          596
          191
          #f)
       '(flags: preserves-marks single-result)
       '(captures:
         (val/ref #%modvars)
         (_cs-x-offset5.0 _cs-y-offset6.0 _all-tags.0 __cs))
       (let ((local705
              (let ((local706 (malloc __cs 'atomic)))
                (begin
                  (set-cpointer-tag! local706 _all-tags.0)
                  (ptr-set!
                   local706
                   _double
                   'abs
                   (#%checked _cs-x-offset5.0)
                   '1.0)
                  (ptr-set! local706 _double 'abs _cs-y-offset6.0 '2.0)
                  local706))))
         (let ((flonum721
                (fl+
                 '0.0
                 (fl+
                  (ptr-ref local705 _double 'abs '0)
                  (ptr-ref local705 _double 'abs '8)))))
           (let ((flonum734
                  (fl+
                   flonum721
                   (fl+
                    (ptr-ref local705 _double 'abs '0)
                    (ptr-ref local705 _double 'abs '8)))))
             (let ((flonum747
                    (fl+
                     flonum734
                     (fl+
                      (ptr-ref local705 _double 'abs '0)
                      (ptr-ref local705 _double 'abs '8)))))
               ((#%closed
                 for-loop22
                 (lambda (arg0-763 argflonum1-764 arg2-765)
                   '#(for-loop
                      #<path:/Users/jay/Dev/scm/github.jeapostrophe/exp/structs/cstruct.rkt>
                      28
                      2
                      656
                      130
                      #f)
                   '(flags: preserves-marks single-result)
                   (if (< arg2-765 '180000)
                     (let ((flonum768
                            (fl+
                             argflonum1-764
                             (fl+
                              (ptr-ref arg0-763 _double 'abs '0)
                              (ptr-ref arg0-763 _double 'abs '8)))))
                       (let ((local781 (+ (#%sfs-clear arg2-765) '1)))
                         (if (< local781 '180000)
                           (let ((flonum786
                                  (fl+
                                   flonum768
                                   (fl+
                                    (ptr-ref arg0-763 _double 'abs '0)
                                    (ptr-ref arg0-763 _double 'abs '8)))))
                             (let ((local799 (+ (#%sfs-clear local781) '1)))
                               (if (< local799 '180000)
                                 (let ((flonum804
                                        (fl+
                                         flonum786
                                         (fl+
                                          (ptr-ref arg0-763 _double 'abs '0)
                                          (ptr-ref
                                           arg0-763
                                           _double
                                           'abs
                                           '8)))))
                                   (let ((local817
                                          (+ (#%sfs-clear local799) '1)))
                                     (if (< local817 '180000)
                                       (for-loop22
                                        arg0-763
                                        (fl+
                                         flonum804
                                         (fl+
                                          (ptr-ref arg0-763 _double 'abs '0)
                                          (ptr-ref
                                           (#%sfs-clear arg0-763)
                                           _double
                                           'abs
                                           '8)))
                                        (+ local817 '1))
                                       flonum804)))
                                 flonum786)))
                           flonum768)))
                     argflonum1-764)))
                local705
                (fl+
                 flonum747
                 (fl+
                  (ptr-ref local705 _double 'abs '0)
                  (ptr-ref (#%sfs-clear local705) _double 'abs '8)))
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
      (let ((localv852 ?) (localv853 ?) (localv854 ?) (localv855 ?))
        (begin
          (set!-values (localv852 localv853 localv854 localv855)
            (time-apply
             (lambda ()
               '.../more-scheme.rkt:336:52
               '(captures: (val/ref #%modvars) (|_test-fun:P@(submod "..")|))
               (|_test-fun:P@(submod "..")|))
             '()))
          (begin
            (printf
             '"cpu time: ~s real time: ~s gc time: ~s\n"
             (#%sfs-clear localv853)
             (#%sfs-clear localv854)
             (#%sfs-clear localv855))
            (apply values (#%sfs-clear localv852))))))
     (#%apply-values
      |_print-values:p@(lib "racket/private/modbeg.rkt")|
      (let ((localv864 ?) (localv865 ?) (localv866 ?) (localv867 ?))
        (begin
          (set!-values (localv864 localv865 localv866 localv867)
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
             (#%sfs-clear localv865)
             (#%sfs-clear localv866)
             (#%sfs-clear localv867))
            (apply values (#%sfs-clear localv864)))))))))
