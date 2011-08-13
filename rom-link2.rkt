#lang racket
(require racket/cmdline)

(define wahcade-lst
  (command-line #:program "rom-link2" 
                #:args (wahcade-lst) wahcade-lst))

(define (linkum name rom)
  (define rom-pth  
    (build-path (current-directory) 
                "Roms"
                (string-append rom ".nes")))
  (define link-pth  
    (build-path (current-directory)
                "Romsl"
                (string-append name ".nes")))
  (unless (file-exists? rom-pth)
    (printf "~v\n" (list wahcade-lst name rom rom-pth))
    (exit 1))
  (make-file-or-directory-link rom-pth link-pth))

(let loop ([ls (file->lines wahcade-lst)])
  (unless (empty? ls)
    (define-values (fi nls) (split-at ls 13))
    (match fi
      [(list (? string? rom) (? string? name) "" "" "" "" "" "" "" "" "" "" "")
       (linkum name rom)]
      [_
       (error 'rom-link2 "~S" fi)])
    (loop nls)))