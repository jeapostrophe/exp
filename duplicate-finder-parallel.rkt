#lang racket
(require openssl/sha1)

(provide main)

(define (find-duplicates directory)
  (printf "Finding in ~a\n" directory)
  (define file-hash (make-hash))
  (define place-list
    (for/fold
     ([ps empty])
     ([f (directory-list directory)])
     (define full-path (build-path directory f))
     (cond
      [(directory-exists? full-path)
       (cons (place-find-duplicates-spawn full-path)
             ps)]
      [else
       (hash-cons! file-hash
                   ;; I had an idea to first find out the things
                   ;; that are the same size and then go back and
                   ;; in parallel check each of their sha1
                   ;; checksums, but just changing this line only
                   ;; save 30 ms, so it probably isn't worth it.
                   #;(file-size full-path)
                   (call-with-input-file full-path sha1)
                   full-path)
       ps])))
  (for ([p place-list])
       (combine-hash! file-hash
                      (place-channel-get p)))
  file-hash)

(define (print-duplicates file-hash)
  (for ([l (hash-values file-hash)]
        #:when (> (length l) 1))
       (printf "duplicates:~n")
       (for ([p l])
            (printf "\t~a~n" p))
       (newline)))

(define (hash-cons! h k v)
  (hash-update! h k (curry cons v) empty))

(define (hash-append! h k val-list)
  (hash-update! h k (curry append val-list) empty))

(define (combine-hash! h assocs)
  (for ([(k vs) (in-dict assocs)])
       (hash-append! h k vs)))

(define (place-find-duplicates-spawn pth)
  (define p (place ch (place-find-duplicates ch)))
  (place-channel-put p pth)
  p)

(define (place-find-duplicates ch)
  (define directory (place-channel-get ch))
  (define file-hash (find-duplicates directory))
  (place-channel-put ch (hash->list file-hash)))

(define (main)
  (time
   (define p (place-find-duplicates-spawn "/home/jay/Downloads/kdict"))
   (print-duplicates (make-hash (place-channel-get p)))))

