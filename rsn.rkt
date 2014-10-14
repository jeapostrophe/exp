#lang racket/base
(require racket/file
         racket/system
         racket/list)

(define set-rx #rx" \\[(.+)\\]\\.rsn$")
(define (unrar rd src dest)
  (define ps
    (map second (filter list? (list-tail (fourth (file->list rd)) 4))))
  (for ([p (in-list ps)])
    (define set
      (string-append (second (regexp-match set-rx p)) ".rsn"))
    (define rn
      (regexp-replace set-rx p ""))
    (define dest-rn
      (build-path dest rn))
    (unless (directory-exists? dest-rn)
      (make-directory dest-rn)
      (parameterize ([current-directory dest-rn])
        (system* (find-executable-path "unrar") "x" (build-path src set))))))

(define (bytes->cstr bs)
  (bytes->string/utf-8
   (subbytes bs 0
             (for/or ([b (in-bytes bs)]
                      [i (in-naturals)])
               (and (zero? b) i)))))

(define (rename p)
  (for ([d (in-list (directory-list p))])
    (define dp (build-path p d))
    (for ([s (in-list (directory-list dp))]
          #:when (regexp-match #rx"spc$" s))
      (define sp (build-path dp s))
      (define ip (open-input-file sp))
      (file-position ip #x2E)
      (define ns (bytes->cstr (read-bytes 32 ip)))
      (close-input-port ip)
      (define nsp (build-path dp (format "~a.spc" ns)))
      (rename-file-or-directory sp nsp))))

(module+ main
  (require racket/cmdline)
  (when #t
    (command-line #:program "rsn"
                  #:args (dest)
                  (rename (path->complete-path dest))))
  (when #f
    (command-line #:program "rsn"
                  #:args (rd src dest)
                  (unrar (path->complete-path rd)
                         (path->complete-path src)
                         (path->complete-path dest)))))
