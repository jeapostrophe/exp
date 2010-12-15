#lang scribble/doc
@(require scribble/manual
          scribble/bnf
          scribble/eval
          (for-label racket/base
                     racket/contract
                     racket/list)

@(define xml-eval (make-base-eval))
@(define plist-eval (make-base-eval))
@interaction-eval[#:eval xml-eval (require xml)]
@interaction-eval[#:eval xml-eval (require racket/list)]
@interaction-eval[#:eval plist-eval (require xml/plist)]

@title{@bold{XML}: Parsing and Writing}

@author["Paul Graunke and Jay McCarthy"]

@defmodule[xml]