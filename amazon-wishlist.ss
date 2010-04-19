(module wish mzscheme
  (require (lib "list.ss")
           (lib "pretty.ss")
           (lib "xml.ss" "xml")
           (lib "uri-codec.ss" "net")
           (lib "url.ss" "net")
           (planet "list.ss" ("jaymccarthy" "mmss.plt" 1))
           (only (planet "ssax.ss" ("lizorkin" "ssax.plt" 1 3))
                 ssax:xml->sxml)
           (planet "sxml.ss" ("lizorkin" "sxml.plt" 1 4)))
  
  (current-alist-separator-mode 'amp)
  
  (define (make-wish-url i)
    (make-url 
     "http"
     #f
     "xml.amazon.com"
     #f
     #t
     (list (make-path/param "onca" empty)
           (make-path/param "xml3" empty))
     (list (cons 't "kevindonahue-20")
           (cons 'dev-t "D6NAM8O51QUSE")
           (cons 'WishlistSearch "STV061I2MKRE")
           (cons 'type "lite")
           (cons 'f "xml")
           (cons 'page (number->string i)))
     #f))
  
  (define (wishlist-page-xml i)
    (define port 
      (get-pure-port
       (make-wish-url i)))
    (begin0 (ssax:xml->sxml port empty)
            (close-input-port port)))
  
  (define (wishlist-books i)
    ((sxpath "//Details[Catalog = 'Book']")
     (wishlist-page-xml i)))
  
  (define (wishlist-records i)
    (map wishlist-record
         (wishlist-books i)))
  
  (define (cadar* p)
    (with-handlers ([exn:fail? (lambda _ "")])
      (cadar p)))
  
  (define (take i l)
    (reverse
     (let loop ([i i] [l l] [r empty])
       (cond
         [(zero? i) r]
         [(empty? l) r]
         [else
          (loop (sub1 i) (rest l) (list* (first l) r))]))))
  
  (define (wishlist-record sx)
    (list (cadar* ((sxpath "//ProductName") sx))
          (apply string-append
                 (between " " 
                          (between "and" 
                                   (map cadr
                                        (take 3
                                              ((sxpath "//Authors/Author") sx))))))
          (cadar* ((sxpath "//ReleaseDate") sx))
          (cadar* ((sxpath "//ListPrice") sx))
          (cadar* ((sxpath "//OurPrice") sx))
          (cadar* ((sxpath "//UsedPrice") sx))))
  
  (define (wishlist-records-all)
    (let loop ([i 1] [r empty] [prev #f])
      #;(printf "Page ~a: ~S~n" (sub1 i) prev)
      (let ([cur (wishlist-records i)])
        (if (equal? cur prev)
            (apply append (reverse r))
            (loop (add1 i) (list* cur r) cur)))))
  
  (display-xml/content
   (xexpr->xml
    `(html (head (title "Jay McCarthy's Amazon Wishlist"))
           (body
            (table (tr (th "Title") (th "Author") (th "Release")
                       (th "New") (th "Amazon") (th "Used"))
                   ,@(map (lambda (r)
                            `(tr ,@(map (lambda (a)
                                          `(td ,a))
                                        r)))
                          (wishlist-records-all))))))))