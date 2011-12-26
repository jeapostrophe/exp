#lang racket

(define p "/home/jay/Dev/scm/github.jeapostrophe/home/etc/keychain")

(define (parse-dump)
  (if (eof-object? (peek-byte))
      empty
      (cons (parse-entry)
            (parse-dump))))

(define (parse-entry)
  (match-define (regexp "^keychain: ") (read-line))
  (match-define (or (regexp "^class: 0x(.*?) *$" 
                            (list _ (app string->number class)))
                    (regexp "^class: \"(.*?)\" *$" 
                            (list _ class)))
                (read-line))
  (match-define "attributes:" (read-line))
  (define attrs (make-hash))
  (parse-attributes attrs)
  (match-define "data:" (read-line))
  (define data (parse-data-segment))
  (list class attrs 
        (format "~a (~a)"
                (or (hash-ref attrs "svce" #f)
                    (hash-ref attrs "srvr" #f))
                (hash-ref attrs "acct" #f))
        data))

(require xml)
(define (parse-data-segment)
  (match (read-line)
         ["" #f]
         [(regexp "^\"(.*)\"$" (list _ d)) d]         
         [(regexp "^0x[^ ]*  \"(.*)\"$" (list _ d))
          (cond
           [(regexp-match #rx"xml" d)
            (string->xexpr
             (regexp-replace* "\\\\011" 
                              (regexp-replace* "\\\\012" d "\n")
                              "\t"))]
           [else d])]))

(define (parse-attributes attrs)
  (when (string=? (peek-string 4 0) "    ")
        (parse-attribute attrs)
        (parse-attributes attrs)))

(define (parse-attribute attrs)
  (match (read-line)
         [(or (regexp "^    0x([^ ]+) <([^>]+)>=(.*?) *$"
                      (list _ (app string->number prop ) type data))
              (regexp "^    \"([^ \"]+)\"<([^>]+)>=(.*?) *$"
                      (list _ prop type data)))
          (define v (parse-data type data))
          (when v (hash-set! attrs prop v))]))

(define parse-data
  (match-lambda*
   [(list _ "<NULL>")
    #f]
   [(list (or "sint32" "uint32") (regexp "0x(.+)" (list _ d)))
    (string->number d)]
   [(list "uint32" d)
    (with-input-from-string d read)]
   [(list "blob" d)
    (with-input-from-string d read)]
   [(list "timedate" _)
    #f]))

(define es
  (with-input-from-file p parse-dump))

(printf "* Imported\n")
(for ([e (in-list (sort es string-ci<=? #:key third))])
     (match-define (list class attrs label data) e)
     (match class
            [(or "inet" "genp")
             (printf "** ~a\n  ~a\n"
                     label
                     data)]
            [c
             #;(eprintf "Ignoring ~v\n" class)
             (void)]))
