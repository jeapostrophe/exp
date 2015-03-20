#!/usr/bin/env racket
#lang racket/base
(require racket/file
         racket/match
         racket/system
         racket/list)

(define mame-dir "/Users/jay/Downloads/Roms/Arcade/mame0159-64bit")
(define roms-dir (build-path mame-dir "roms"))
(define last-path (build-path mame-dir "last.rktd"))

(define games
  `("tgm2p"
    "futari15"
    "deathsml"
    ["bublbobl_orig.zip" "bublbobl.zip" "bublbobl"]
    ;; "espgal2"
    
    "miexchng"
    "futariblj"
    "dsmbl"
    ["bublcave.zip" "bublbobl.zip" "bublbobl"]
    ;;"ddpdfk"
    ;;"rsgun"
    ))

(module+ main
  (define last-one
    (if (file-exists? last-path)
        (file->value last-path)
        -1))
  (define next-one
    (modulo (add1 last-one) (length games)))
  (define next (list-ref games next-one))
  (write-to-file next-one last-path
                 #:exists 'replace)
  (define-values (rom-name extra-args)
    (match next
      [(? string? rom)
       (values rom empty)]
      [(list* real-path link-path rom extra-args)
       (define full-link-path (build-path roms-dir link-path))
       (when (link-exists? full-link-path)
         (delete-file full-link-path))
       (make-file-or-directory-link (build-path roms-dir real-path)
                                    full-link-path)
       (values rom extra-args)]))
  (parameterize ([current-directory mame-dir])
    (apply
     system* (build-path mame-dir "mame64")
     rom-name
     "-skip_gameinfo"
     (if (empty? extra-args)
         (list "-autosave")
         extra-args))))
