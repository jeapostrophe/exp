#lang racket/base
(require racket/list
         racket/string
         racket/runtime-path)

(define MIN 2)

(define-runtime-path dict-raw "/usr/share/dict/words")
(define-runtime-path dict-compiled "dict.rktd")

(struct word-list (is-a-word? even-c odd-c suffix) #:mutable #:prefab)
(define (make-empty-word-list)
  (word-list #f 0 0 (make-hasheq)))

(define (word-list-add! wl str)
  (word-list-add-chars! wl (string->list str)))
(define (word-list-add-chars! wl cs)
  (unless (word-list-is-a-word? wl)
    (cond
      [(empty? cs)
       ;; Mark this as a word
       (set-word-list-is-a-word?! wl #t)
       (set-word-list-even-c! wl (add1 (word-list-even-c wl)))]
      [else
       ;; Make a new word list for the suffix
       (define n-wl
         (hash-ref! (word-list-suffix wl) (first cs) make-empty-word-list))
       ;; Update the counts
       (if (even? (length cs))
         (set-word-list-even-c! wl (add1 (word-list-even-c wl)))
         (set-word-list-odd-c! wl (add1 (word-list-odd-c wl))))
       ;; Recur and add the tail
       (word-list-add-chars! n-wl (rest cs))])))
(define (word-list->list wl)
  (if (word-list-is-a-word? wl)
    (list empty)
    (append*
     (for/list ([(c n-wl) (in-hash (word-list-suffix wl))])
       (map (λ (ns) (cons c ns))
            (word-list->list n-wl))))))
(define (word-list->string prefix wl)
  (string-join
   (for/list ([w (in-list (word-list->list wl))])
     (apply string (append (reverse prefix) w)))))

(unless (file-exists? dict-compiled)
  (define *wl* (make-empty-word-list))

  (with-input-from-file dict-raw
    (λ ()
      (for ([l (in-lines)])
        (when ((string-length l) . > . MIN)
          (word-list-add! *wl* (string-downcase l))))))

  (with-output-to-file dict-compiled
    #:exists 'replace
    (λ ()
      (write *wl*))))

(define (play wl w players-turn?)
  (cond
    [(or (not wl) (word-list-is-a-word? wl))
     (if players-turn?
       (printf "The computer lost.\n")
       (printf "The player lost.\n"))]
    [else
     (printf "The prefix is: ~a\n" (list->string (reverse w)))
     (define nc
       (cond
         [players-turn?
          (printf "What's your letter? ")
          (string-ref (read-line) 0)]
         [else
          (define-values
            (nc n-wl %)
            (for/fold ([nc #f] [* #f] [% -inf.0])
                ([(c n-wl) (in-hash (word-list-suffix wl))])
              (define n-%
                (/ (word-list-odd-c n-wl)
                   (+ (word-list-odd-c n-wl)
                      (word-list-even-c n-wl))))
              (if (n-% . > . %)
                (values c n-wl n-%)
                (values nc * %))))
          (printf "The computer choose ~a (~a ~a ~a).\n\t~e\n"
                  (string nc)
                  (word-list-odd-c n-wl)
                  (word-list-even-c n-wl)
                  %
                  (word-list->string (list* nc w) n-wl))
          nc]))
     (play (hash-ref (word-list-suffix wl) nc #f)
           (list* nc w)
           (not players-turn?))]))

(module+ main
  (play (with-input-from-file dict-compiled read) empty
        (zero? (random 2))))
