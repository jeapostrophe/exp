#lang racket/base
(require racket/list
         racket/string)

(define (build-rx ws)
  (unless (= 1 (length (remove-duplicates (map string-length ws))))
    (error 'typeshift "Unequal length input or no input: ~v" ws))
  (define tpos
    (for/list ([i (in-range (string-length (first ws)))])
      (define os (map (λ (w) (char-downcase (string-ref w i))) ws))
      (apply string (append (list #\[) os (list #\])))))  
  (regexp (string-append (string-append* "^" tpos) "$")))

(define (solve in)
  (define r (build-rx (string-split in "\n")))
  (with-input-from-file "/Users/jay/Dev/dist/dwyl/english-words/words3.txt"
    (λ ()
      (for ([l (in-lines)]
            #:when (regexp-match r l))
        (displayln l)))))

(module+ main
  (solve #<<END
V N A
LAIAO
OIRYS
KRJUF
END
         ))
