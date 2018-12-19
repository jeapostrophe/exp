#lang racket/base
(require racket/list
         racket/file
         racket/format
         racket/match)

(module+ main
  (define h (current-directory))

  (define starting-index (hash "AFFC" -3
                               "ADWD" -6))
  (define book->ch->file (make-hash))
  (for ([b (in-list '("AFFC" "ADWD"))])
    (define ch->file (make-hash))
    (hash-set! book->ch->file b ch->file)
    (define ch (hash-ref starting-index b))
    (for ([f (in-directory (build-path h b "text"))])
      (unless (< (file-size f) 1024)
        (hash-set! ch->file ch f)
        (set! ch (add1 ch)))))

  (define d (build-path h "AFFD"))
  (make-directory* d)  
  
  (for ([p (in-list (file->lines (build-path h "audiobook.txt")))])
    (match-define (regexp #rx"^[0-9]+ AFFD-([0-9]+) (....)-([0-9]+) (.*?)\\.mp3$"
                          (list _ final-ch book (app string->number book-ch) title))
      p)
    (define dest (build-path d (~a "AFFD-" final-ch " " book "-" book-ch " " title ".html")))
    (define src (hash-ref (hash-ref book->ch->file book) book-ch))
    (copy-file src dest)))
