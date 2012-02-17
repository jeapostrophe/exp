#lang racket
(require file/md5)

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
       (define p (place ch (place-find-duplicates ch)))
       (place-channel-put p full-path)
       (cons p ps)]
      [else
       (add-or-append! file-hash
                       (md5 (file->bytes full-path))
                       (list full-path))
       ps])))
  (for ([p place-list])
       (define assocs (place-channel-get p))
       (combine-hash! file-hash assocs))
  file-hash)

(define (print-duplicates file-hash)
  (for ([l (hash-values file-hash)])
       (when (> (length l) 1)
             (printf "duplicates:~n")
             (for ([p l])
                  (printf "\t~a~n" p))
             (newline))))

(define (add-or-append! h k val-list)
  (hash-update! h k (curry append val-list) empty))

(define (combine-hash! h assocs)
  (for ([p assocs])
       (add-or-append! h (first p) (rest p))))

(define (place-find-duplicates ch)
  (define directory (place-channel-get ch))
  (define file-hash (find-duplicates directory))
  (place-channel-put ch (hash->list file-hash)))

(define (main)
  (define p (place ch (place-find-duplicates ch)))
  (place-channel-put p "/home/jay/Downloads/kdict")
  (print-duplicates (make-hash (place-channel-get p))))

