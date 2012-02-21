#lang racket
(require xml
         net/url
         (planet neil/html-parsing/html-parsing)
         (planet clements/sxml2))

(define (wishlist-url page)
  (format "http://www.amazon.com/registry/wishlist/STV061I2MKRE/ref=cm_wl_sb_o?reveal=unpurchased&filter=all&sort=date-added&layout=compact&x=17&y=8&page=~a" page))

(define u (wishlist-url 1))
(define xe (call/input-url (string->url u) get-pure-port html->xexp))
(define items
  ;; tr/td/span[@class=\"small productTitle\"]
  ((sxpath "//table[@class=\"compact-items wlrdZeroTable\"]/tbody[@class=\"itemWrapper\"]") xe))

(require racket/pretty)
(pretty-print
 items)
