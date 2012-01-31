#lang racket
(require racklog)
; http://www.csupomona.edu/~jrfisher/www/prolog_tutorial/2_1.html


(define %adjacent 
    (%rel ()
          [('a1 'a2)]
          [('a2 'a1)]
          [('a1 'a3)]
          [('a1 'a4)]
          [('a1 'a5)]
          [('a2 'a3)]
          [('a2 'a4)]
          [('a3 'a4)]
          [('a4 'a5)]
          [('a3 'a1)]
          [('a4 'a1)]
          [('a5 'a1)]
          [('a3 'a2)]
          [('a4 'a2)]
          [('a4 'a3)]
          [('a5 'a4)]))

; check it's working
(%which () (%adjacent 'a1 'a2))
(%which () (%adjacent 'a5 'a3))

(define %color
    (%rel ()
          [('a1 'red    'a)] [('a1 'red   'b)]
          [('a2 'blue   'a)] [('a2 'blue  'b)]
          [('a3 'green  'a)] [('a3 'green 'b)]
          [('a4 'yellow 'a)] [('a4 'blue  'b)]
          [('a5 'blue   'a)] [('a5 'green 'b)]))


;; option A
(define %conflict-a
  (%let (X Y Color)
        (%rel (Coloring )
              [(Coloring)
               (%adjacent X Y)
               (%color X Color Coloring)
               (%color Y Color Coloring)])))

;; option B
(define %conflict-b
  (%let (X Y Color)
        (%rel (Coloring)
              [(Coloring)
               (%adjacent X Y)
               (%color X Color Coloring)
               (%color Y Color Coloring)])))


(%which () (%conflict-a 'a)); expecting #f , got #<procedure>
(%which () (%conflict-a 'b)); expecting '() , got #<procedure>

(%which () (%conflict-b 'a)); expecting #f , got #<procedure>
(%which () (%conflict-b 'b)); expecting '() , got #<procedure>
