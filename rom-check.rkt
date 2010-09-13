#lang racket

;; Configuration
(define
  wahcade-list
  "/home/jay/.wahcade/files/mednafen-nes-1.lst")

(define
  rom-home
  "/home/jay/Games/Nintendo - NES/")

;; Work
(define roms
  (let loop ([ls (file->lines wahcade-list)])
    (if (empty? ls)
        empty
        (let-values ([(fi ls) (split-at ls 13)])
          (match fi
            [(list (? string?) (? string?) "" "" "" "" "" "" "" "" "" "" "")
             (void)]
            [_
             (error 'bad-rom "~S" fi)])
          (list* (first fi) (loop ls))))))

(define dirs
  (list "Box" "Cart" "Titles"))

(define dir->list
  (for/hash ([d (in-list dirs)])
    (values d (map path->string
                   (directory-list (build-path rom-home d))))))

(define (rom.ext r dir)
  (format "~a.~a" r
          (match dir
            ["Box" "jpg"]
            ["Cart" "jpg"]
            ["Snaps" "png"]
            ["Titles" "png"])))

(define (suffixes w)
             (list* w (cond [(empty? w) empty]
                            [(cons? w) (suffixes (rest w))])))

(for ([r (in-list roms)])
  (define words (regexp-split #rx" +" r))
  
  (define prefixes
    (filter-map (λ (ws)
                  (and (not (empty? ws))
                       (apply string-append (add-between (reverse ws) " "))))
                (suffixes (reverse words))))
  (for ([d (in-list dirs)])
    (define r.ext (rom.ext r d))
    (define in-d (hash-ref dir->list d))
    (unless (member r.ext in-d)
      (let ()
        (define in-d*match
          (filter-map (λ (f)
                        (define f-len (string-length f))
                        (for/or ([p (in-list prefixes)]
                                 [i (in-naturals)])
                          (define p-len (string-length p))
                          (and (p-len . <= . f-len)
                               (string=? p (substring f 0 p-len))
                               (cons i f))))
                      in-d))
        (define matches
          (sort in-d*match <= 
                #:key car))
        (define N 10)
        (define similar
          (for/list ([m (in-list matches)]
                     [i (in-range N)])
            (cdr m)))
        (define (swap! one)
          (rename-file-or-directory (build-path rom-home d one)
                                    (build-path rom-home d r.ext))          
          (printf "Moved ~a to ~a\n" one r.ext))
        
        (if (empty? similar)
            (eprintf "~a (and nothing similar) exist in ~a\n" r.ext d)
            (let ()
              (printf "~a does not exist in ~a\n" r.ext d)
              (for ([i (in-naturals)]
                    [f (in-list similar)])
                (printf "\t~a. ~a\n" i f))
              (define how-many (length similar))
              
              (let loop ()
                (define selection (read))
                (if (number? selection)
                    (if (selection . < . how-many)
                        (swap! (list-ref similar selection))
                        (loop))
                    (eprintf "Skipping ~a in ~a\n" r.ext d)))))))))
