#lang racket

(define spaces-pth
  "/home/jay/Dev/scm/github.jeapostrophe/home/etc/spaces")

(define (snoc/flip x l)
  (append l (list x)))

(define-values (space->script _)
  (for/fold ([space->script (hash)]
             [current #f])
      ([l (in-list (file->lines spaces-pth))])
    (match current
      [#f
       (match l
         [(regexp #rx"^# (.+)$" (list _ space))
          (values space->script space)])]
      [""
       (values space->script #f)]
      [(? string?)
       (match l
         [""
          (values space->script #f)]
         [(? string?)
          (values
           (hash-update space->script current (curry snoc/flip l) empty)
           current)])])))

(define space
  (command-line
   #:args (space) space))

(define matches
  (filter (curry regexp-match (regexp-quote space))
          (hash-keys space->script)))

(match matches
  [(list x)
   (define p (make-temporary-file))
   (with-output-to-file p
     #:exists 'replace
     (λ ()
       (for ([l (in-list (hash-ref space->script x))])
         (printf "~a &>/dev/null &\n" l))))
   (system (format "exec zsh -i ~s" (path->string p)))]
  [_
   (system (format "exec xmessage ~s" (format "Space name is not unique: ~e" matches)))])
