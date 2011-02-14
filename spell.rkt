#lang racket
(require racket/runtime-path)

(define MIN 2)
(define compile? #f)

(command-line #:program "spell"
              #:once-any
              ("--compile" "Compile the dictionary"
                           (set! compile? #t)))

(define-runtime-path dict-raw "/usr/share/dict/words")
(define-runtime-path dict-compiled "dict.rktd")

(struct word-list (is-a-word? even-c odd-c suffix) #:mutable #:prefab)
(define (make-empty-word-list)
  (word-list #f 0 0 (make-hasheq)))

(define (word-list-add! wl str)
  (word-list-add-chars! wl (string->list str)))
(define (word-list-add-chars! wl cs)
  (unless (word-list-is-a-word? wl)
    (if (empty? cs)
        (begin
          ; Mark this as a word
          (set-word-list-is-a-word?! wl #t)
          (set-word-list-even-c! wl (add1 (word-list-even-c wl))))
        (let ()
          ; Make a new word list for the suffix
          (define n-wl
            (hash-ref! (word-list-suffix wl) (first cs) make-empty-word-list))
          ; Update the counts
          (if (even? (length cs))
              (set-word-list-even-c! wl (add1 (word-list-even-c wl)))
              (set-word-list-odd-c! wl (add1 (word-list-odd-c wl))))
          ; Recur and add the tail
          (word-list-add-chars! n-wl (rest cs))))))

(when compile?
  (define *wl* (make-empty-word-list))
  
  (with-input-from-file dict-raw
    (λ ()
      (for ([l (in-lines)])
        (when ((string-length l) . > . MIN)
          (word-list-add! *wl* (string-downcase l))))))
  
  (with-output-to-file dict-compiled
    #:exists 'replace
    (λ ()
      (write *wl*)))
  
  (exit 0))

(define (play wl w players-turn?)
  (cond
    [(or (not wl) (word-list-is-a-word? wl))
     (if players-turn?
         (printf "The computer lost.\n")
         (printf "The player lost.\n"))]
    [else
     (printf "The prefix is: ~a\n" (list->string (reverse w)))
     (define nc
       (if players-turn?
           (let ()
             (printf "What's your letter? ")
             (string-ref (read-line) 0))
           (let ()
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
             (printf "The computer choose ~a (~a ~a ~a).\n"
                     (string nc)
                     
                     (word-list-odd-c n-wl)
                     (word-list-even-c n-wl)
                     %
                     
                     )
             nc)))
     (play (hash-ref (word-list-suffix wl) nc #f)
           (list* nc w)
           (not players-turn?))]))

(play (with-input-from-file dict-compiled read) empty
      (zero? (random 2)))