#!/usr/bin/env racket
#lang racket/base
(require racket/pretty
         racket/file
         racket/match)

(pretty-print
 (match (current-command-line-arguments)
   [(vector) (read)]
   [(vector p) (file->value p)]))
