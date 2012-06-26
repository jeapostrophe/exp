#lang racket
(require (planet neil/csv))

(csv-for-each
 (match-lambda
  [(list Author Title Price)
   (printf "** [[http://www.google.com/search?tbm=bks&q=~a by ~a][~a, by ~a]]\n"
           Title Author
           Title Author)])
 (open-input-file "/home/jay/Downloads/wishlist.csv"))
