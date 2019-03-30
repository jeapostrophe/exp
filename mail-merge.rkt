#lang racket/base
(require racket/match csv-reading)

(define (mail! to-name to-email subject message)
  (define-values
    (sp _stdout stdin _stderr)
    (subprocess (current-output-port) #f (current-error-port)
                "/usr/local/bin/msmtp"
                to-email))
  (fprintf stdin "From: Jay McCarthy <jay.mccarthy@gmail.com>\n")
  (fprintf stdin "To: ~a <~a>\n" to-name to-email)
  (fprintf stdin "Subject: ~a\n" subject)
  (fprintf stdin "\n")
  (fprintf stdin "~a\n "message)
  (fprintf stdin "\n")
  (fprintf stdin SIG)
  (close-output-port stdin)
  (subprocess-wait sp))

(module+ main
  #;(mail! "Libby McCarthy" "libbydmccarthy@gmail.com"
           "A Test Merge" "A test message")

  (define subject (vector-ref (current-command-line-arguments) 0))
  
  (define next-row ((make-csv-reader-maker '()) (current-input-port)))
  (void (next-row))
  (csv-for-each
   (match-lambda
     [(list _ fname lname to-email _ message)
      (define to-name
        (cond
          [(and (string=? "" fname) (string=? "" lname)) to-email]
          [(or (string=? "" fname) (string=? "" lname)) (string-append fname lname)]
          [else (string-append fname " " lname)]))
      (mail! to-name to-email subject message)
      (sleep 1)])
   next-row))

(define SIG
  #<<END
--
Jay McCarthy
Associate Professor @ CS @ UMass Lowell
http://jeapostrophe.github.io
Vincit qui se vincit.
END
  )
