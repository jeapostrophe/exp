#lang scribble/doc
@(require scribble/manual
          scribble/bnf
          scribble/eval
          (for-label racket/base
                     racket/contract
                     racket/match
                     racket/list))

@(define our-eval (make-base-eval))

@title{@bold{Temporal Contracts}: Explicit Contract Monitors}

@author[@author+email["Jay McCarthy" "jay@racket-lang.org"]]

@defmodule[temp-c]

The contract system implies the presence of a "monitoring system" that ensures that contracts are not violated. The @racketmodname[racket/contract] system compiles this monitoring system into checks on values that cross a contracted boundary. This module provides a facility to pass contract boundary crossing information to an explicit monitor for approval. This monitor may, for example, use state to enforce temporal constraints, such as a resource is locked before it is accessed.

@section[#:tag "monitor"]{Monitors}

@defmodule[temp-c/monitor]
@(require (for-label "../monitor.rkt"))
@interaction-eval[#:eval our-eval (require "../monitor.rkt" racket/contract racket/match)]

@deftogether[[
@defstruct*[monitor ([label symbol?]) #:transparent]
@defstruct*[(monitor:proj monitor)
            ([label symbol?] [proj-label symbol?] [v any/c])
             #:transparent]
@defstruct*[(monitor:call monitor)
            ([label symbol?] [proj-label symbol?] [f procedure?] 
             [app-label symbol?] [kws (listof keyword?)] [kw-args list?] [args list?])
            #:transparent]
@defstruct*[(monitor:return monitor)
            ([label symbol?] [proj-label symbol?] [f procedure?] 
             [app-label symbol?] [kws (listof keyword?)] [kw-args list?] [args list?]
             [rets list?])
             #:transparent]
@defproc[(monitor/c [monitor-allows? (-> monitor? boolean?)]
                    [label symbol?]
                    [c contract?])
         contract?]
]]{
  
  @racket[monitor/c] creates a new contract around @racket[c] that uses @racket[monitor-allows?] to approve
  contract boundary crossings. (@racket[c] approves positive crossings first.)
  
  Whenever a value @racket[v] is projected by the result of @racket[monitor/c], @racket[monitor-allows?]
  must approve a @racket[(monitor:proj label proj-label v)] structure, where @racket[proj-label] is a unique
  symbol for this projection.
  
  If @racket[monitor-allows?] approves and the value is not a function, then the value is returned.
  
  If the value is a function, then a projection is returned, whenever it is called, @racket[monitor-allows?]
  must approve a @racket[(monitor:call label proj-label v app-label kws kw-args args)] structure,
  where @racket[app-label] is a unique symbol for this application and @racket[kws], @racket[kw-args], @racket[args]
  are the arguments passed to the function.
  
  Whenever it returns, @racket[monitor-allows?]
  must approve a @racket[(monitor:return label proj-label v app-label kws kw-args args rets)] structure,
  where @racket[ret] are the return values of the application.
  
  The unique projection label allows explicitly monitored contracts to be useful when used in a first-class way 
  at different boundaries.
  
  The unique application label allows explicitly monitored contracts to pair calls and returns when functions
  return multiple times or never through the use of continuations.
  
}
  
Here is a short example that uses an explicit monitor to ensure that @racket[_malloc] and @racket[_free] are
used correctly.
@racketblock[
 (define allocated (make-weak-hasheq))
 (define memmon
   (match-lambda
     [(monitor:return 'malloc _ _ _ _ _ _ (list addr))
      (hash-set! allocated addr #t)
      #t]
     [(monitor:call 'free _ _  _ _ _ (list addr))
      (hash-has-key? allocated addr)]
     [(monitor:return 'free _ _ _ _ _ (list addr) _)
      (hash-remove! allocated addr)
      #t]
     [_
      #t]))
 (provide/contract
  [malloc (monitor/c memmon 'malloc (-> number?))]
  [free (monitor/c memmon 'free (-> number? void))])
]
           
@section[#:tag "dsl"]{Domain Specific Language}

@defmodule[temp-c/dsl]
@(require (for-label "../dsl.rkt"))
@interaction-eval[#:eval our-eval (require "../dsl.rkt")]

XXX
