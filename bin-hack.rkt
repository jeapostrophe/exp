#lang racket/base
(require racket/file
         racket/set
         racket/match)

(define (go! spec)
  (define vf-hts (make-hasheq))
  (for ([s (in-list spec)]
        [si (in-naturals)])
    (match-define (vector fp vals) s)
    (printf "~a\n" fp)
    (define bs (file->bytes fp))
    (printf "\tlen = ~a\n" (bytes-length bs))
    (for ([b (in-bytes bs)]
          [i (in-naturals)])
      (for ([v (in-list vals)]
            [vi (in-naturals)])
        (define vf-ht (hash-ref! vf-hts vi (λ () (make-hasheq))))
        (when (= b v)
          (hash-update! vf-ht i (λ (old) (cons si old)) null)))))

  (for ([(vi vf-ht) (in-hash vf-hts)])
    (for ([(where who) (in-hash vf-ht)])
      (unless (= 1 (length who))
        (printf "~a = ~a\n" vi (number->string where 16))))))

(module+ main
  (go! (list (vector "continue.sav-LastLevel-26-9" (list 26 9))
             (vector "continue.sav-LastFight-3-12" (list 3 12)))))
