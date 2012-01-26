#lang racket/base
(require racket/list
         racket/port
         net/url)

(define *output-dir* "/tmp/kdict")
(define (jdict-url start)
  (url "http" 
       #f
       "www.saiga-jp.com"
       #f #t
       (list (path/param "cgi-bin" empty)
             (path/param "dic.cgi" empty))
       (list (cons 'm "view")
             (cons 'f "0")
             (cons 'sc "0")
             (cons 'j "")
             (cons 'e "")
             (cons 'g "")
             (cons 's "5")
             (cons 'rt "0")
             (cons 'start (number->string start))
             (cons 'sid "1314972880_86353"))
       #f))

(define (parse u)
  (printf "get: ~a\n" (url->string u))
  (display
   (call/input-url u get-pure-port
                   port->string
                   (list (format "Referer: ~a" (url->string u))))))

(printf "got: ~a\n" "http://www.saiga-jp.com/cgi-bin/dic.cgi?m=view&f=0&sc=0&j=&e=&g=&s=5&rt=0&k=&start=51&sid=1314972880_86353")
(parse (jdict-url 0))
