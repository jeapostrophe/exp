#!/usr/bin/env racket
#lang racket/base
(require racket/pretty
         racket/cmdline
         racket/file)

(command-line #:program "rkt-pretty"
              #:args (p)
              (pretty-print (file->value p)))
