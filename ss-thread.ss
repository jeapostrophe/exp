#lang scheme
(require net/url
         web-server/servlet-dispatch
         web-server/http
         web-server/http/response)

(define current-response-ch (make-thread-cell #f))
(define-struct resumed (tag))
(define-struct resume (req reply-ch))

(define (send/wait-dispatcher conn req)
  (define the-response-ch (make-channel))
  ;; Do the dispatch
  (thread
   (lambda ()
     (thread-cell-set! current-response-ch the-response-ch)
     (let ([v (dispatch req)])
       (if (resumed? v)
           (printf "Resumed an earlier computation: ~S~n" (resumed-tag v))
           (begin (printf "Received a value from the dispatch function: ~S~n" v)
                  (channel-put (thread-cell-ref current-response-ch) v))))))
  (let ([resp (channel-get the-response-ch)])
    (printf "Sending a reply to the client~n")
    (output-response conn resp)))

(define (send/wait mk-page)
  (define request-ch (make-channel))
  (define tag (format "k~a" (current-inexact-milliseconds)))
  (printf "[~S] Creating new tag~n" tag)
  (hash-set! dispatch-table tag
             (lambda (request)
               (printf "[~S] Removing tag~n" tag)
               (hash-remove! dispatch-table tag)
               (printf "[~S] Sending request~n" tag)
               (channel-put request-ch (make-resume request (thread-cell-ref current-response-ch)))
               (make-resumed tag)))
  (printf "[~S] Send back page to abort channel~n" tag)
  (channel-put (thread-cell-ref current-response-ch) (mk-page (string-append "/" tag)))
  (printf "[~S] Waiting for new request~n" tag)
  (match (channel-get request-ch)
    [(struct resume (req new-response-ch))
     (printf "[~S] Received request and new abort ch~n" tag)
     (thread-cell-set! current-response-ch new-response-ch)
     req]))

(define dispatch-table (make-hash))
(define (expiration-handler req)
  (define url (request-uri req))
  `(html (head (title "Error"))
         (body 
          (font ([color "red"])
                "Unknown or expired page: " 
                ,(url->string url)))))
(define (dispatch req)
  (define url (request-uri req))
  ;; Extract the path part:
  (define path (map path/param-path (url-path url)))
  ;; Find a handler based on the path's first element:
  (define handler
    (hash-ref dispatch-table (first path)
              (lambda () expiration-handler)))
  (handler req))

;; ----------------------------------------

(define (get-number which-number)
  (define req
    ;; Generate a URL for the current computation:
    (send/wait
     ;; Receive the computation-as-URL here:
     (lambda (k-url)
       ;; Generate the query-page result for this connection.
       ;; Send the query result to the saved-computation URL:
       `(html
         (head (title "Enter a Number to Add"))
         (body ([bgcolor "white"])
               (form ([action ,k-url] [method "get"])
                     ,which-number " number:"
                     (input ([type "text"]
                             [name "number"]
                             [value ""]))
                     (input ([type "submit"] 
                             [value "Enter"]))))))))
  ;; We resume here later, in a new connection
  (define query (url-query (request-uri req)))
  (string->number (cdr (assq 'number query))))

(define (sum2 req)
  (define m (get-number "First"))
  (define n (get-number "Second"))
  `(html (body "The sum is " ,(number->string (+ m n)))))

(hash-set! dispatch-table "sum2" sum2)

(serve/launch/wait
 (lambda (stop?-sema) send/wait-dispatcher)
 #:launch-path "/sum2")