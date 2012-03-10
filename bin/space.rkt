#lang racket/base
(require racket/list
         racket/match
         racket/file
         racket/function
         racket/cmdline
         racket/system
         ffi/unsafe
         ffi/unsafe/define)

(define-ffi-definer define-libc (ffi-lib #f))
(define-libc execv (_fun _string (_list i _string) -> _int))

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
   (define cmds (hash-ref space->script x))
   (with-output-to-file p
     #:exists 'replace
     (λ ()
       (for ([l (in-list cmds)]
             [i (in-naturals 1)])
         (cond
           [(= i (length cmds))
            (printf "exec ~a\n" l)]
           [(regexp-match #rx"^oe " l)
            (printf "~a &>/dev/null\n" l)]
           [else
            (printf "~a &>/dev/null &\n" l)]))))
   (execv (find-executable-path "zsh")
          (list (find-executable-path "zsh")
                "-i"
                (path->string p)
                #f))]
  [_
   (system (format "exec xmessage ~s" (format "Space name is not unique: ~e" matches)))])
