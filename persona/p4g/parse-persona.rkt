#lang racket/base
(require racket/list
         racket/match
         racket/file)

(define (parse-arcana l)
  (match l
    [(list* 
      (regexp #rx"^==(.+)==$" (list _ (app string->symbol arcana)))
      (regexp #rx"^{\\|" (list _))
      l)
     (let loop ([l l])
       (match l
         [(list-rest (regexp #rx"Level$" (list _))
                     (regexp #rx"Persona$" (list _))
                     l)
          (loop l)]
         [(list-rest (regexp #rx"\\|-" (list _))
                     l)
          (loop l)]
         [(list-rest (regexp #rx"^.+\\|([0-9]+)$" 
                             (list _ (app string->number lvl)))
                     (regexp #rx"^\\|\\[\\[(.+)\\]\\]$"
                             (list _ persona))
                     l)
          (write `(define-persona ,arcana ,lvl ,persona)) (newline)
          (loop l)]
         [(list-rest (regexp #rx"^.+\\| -$" 
                             (list _ ))
                     (regexp #rx"^\\|\\[\\[(.+)\\]\\]$"
                             (list _ persona))
                     l)
          (loop l)]
         [(list-rest (regexp #rx"^\\|}$" (list _))
                     ""
                     l)
          l]))]))

(define (parse-all p)
  (let loop ([l (file->lines p)])
    (unless (empty? l)
      (loop (parse-arcana l)))))

(module+ main
  (require racket/runtime-path)
  (define-runtime-path persona.txt "persona.txt")
  (parse-all persona.txt))
