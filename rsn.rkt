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
  (subbytes bs 0
            (or (for/or ([b (in-bytes bs)]
                         [i (in-naturals)])
                  (and (zero? b) i))
                (bytes-length bs))))

(define (rename rp np)
  (for ([d (in-list (directory-list rp))])
    (define drp (build-path rp d))
    (define dnp (build-path np d))
    (make-directory* dnp)
    (for ([s (in-list (directory-list drp))]
          #:when (regexp-match #rx"spc$" s))
      (printf "\t~a/~a\n" d s)
      (define tr
        (second (regexp-match #rx"^[a-zA-Z0-9]+-(.+) *\\.spc" s)))
      (define sp (build-path drp s))
      (define ip (open-input-file sp))
      (file-position ip #x2E)
      (define ns
        (regexp-replace* #rx"/" (bytes->cstr (read-bytes 32 ip)) "-"))
      (close-input-port ip)
      (define nsp (build-path dnp (format "~a. ~a.spc" tr ns)))
      (define nsp+
        (if (file-exists? nsp)
            (build-path dnp (format "~a. ~a (copy).spc" tr ns))
            nsp))
      (with-handlers ([exn:fail? (λ (x) (displayln (exn-message x)))])
        (rename-file-or-directory sp nsp+)))))

(module+ main
  (require racket/cmdline)
  (when #t
    (command-line #:program "rsn"
                  #:args (rd src dest nice)
                  (rename (path->complete-path dest)
                          (path->complete-path nice))))
  (when #f
    (command-line #:program "rsn"
                  #:args (rd src dest)
                  (unrar (path->complete-path rd)
                         (path->complete-path src)
                         (path->complete-path dest)))))
