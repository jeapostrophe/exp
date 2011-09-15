#lang racket
(require racket/cmdline)

(define dry? #f)
(define-syntax-rule (dry (f a ...))
  (begin
    (printf "~a\n" (list 'f a ...))
    (unless dry?
      (f a ...))))

(define dir
  (command-line #:program "sortdir"
                #:args (dir) dir))

(define fs
  (sort (directory-list dir)
        string-ci<=?
        #:key path->string))

(define tmp
  (build-path dir ".tmp"))

(dry (make-directory tmp))

(for ([f (in-list fs)])
 (dry (rename-file-or-directory
       (build-path dir f)
       (build-path tmp f))))

(for ([f (in-list fs)])
 (dry (rename-file-or-directory
       (build-path tmp f)
       (build-path dir f))))

(dry (delete-directory tmp))
