#lang racket
(require tests/eli-tester)
(test
 (dynamic-require "good-linker1.rkt" #f)
 (dynamic-require "good-linker2.rkt" #f)
 (dynamic-require "bad-linker.rkt" #f))