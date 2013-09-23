#lang racket/base

(module+ test
  (define/dpr (copy-file dst-name src-name)
    (define-values (src serr) (os.Open src-name))
    (when serr
      (return))
    (defer (os.Close src))
    (define-values (dst derr) (os.Create dst-name))
    (when derr
      (return))
    (defer (os.Close dst))
    (return (io.Copy dst src))))
