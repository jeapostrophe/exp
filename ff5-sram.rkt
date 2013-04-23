#! /usr/bin/env racket
#lang racket/base
(require racket/system
         racket/file)

;; Based on http://wiki.superfamicom.org/snes/show/Final+Fantasy+5

(define (save-slot-start i)
  (unless (< i 4)
    (error 'ff5 "There are only four save slots"))
  (* i #x700))

(define (char-slot-offset i)
  (unless (< i 4)
    (error 'ff5 "There are only four characters"))
  (* i #x50))

(define abp-offset #x3B)

(define checksum-offset #x1FF0)

(define big-endian? #f)

(define (modify-sram p which-save)
  (printf "Modifying ~a\n" p)
  (define sram (file->bytes p))

  (define save-start (save-slot-start which-save))
  (for ([i (in-range 4)])
    (define char-start (char-slot-offset i))
    (define this-abp-offset 
      (+ save-start char-start abp-offset))
    (printf "~a: ~a -> 999\n"
            i
            (integer-bytes->integer
             sram
             #f big-endian?
             this-abp-offset
             (+ this-abp-offset 2)))

    (integer->integer-bytes 999 2
                            #f big-endian?
                            sram this-abp-offset))

  (printf "Computing checksum\n")
  (define-values (final-checksum final-carry)
    (for/fold ([aw 0] [carry 0])
        ;; It is #x600 bytes, but the checksum is based on 16-bits
        ([i (in-range (/ #x600 2))])
      (define word-start
        (+ save-start (* i 2)))
      (define rw
        (integer-bytes->integer
         sram
         #f big-endian?
         word-start
         (+ word-start 2)))
      (define maybe-checksum
        (+ aw rw carry))
      (define new-checksum
        (modulo maybe-checksum (expt 2 16)))
      (values new-checksum
              (if (= new-checksum maybe-checksum)
                0
                1))))
  
  (printf "Fixing checksums...\n")
  (define checksum-start
    (+ checksum-offset
       ;; 16-bits per save
       (* which-save 2)))
  (integer->integer-bytes final-checksum 2
                          #f big-endian?
                          sram checksum-start)

  (display-to-file sram p
                   #:exists 'replace)

  (void))

(module+ main
  (require racket/cmdline)
  (command-line #:program "ff5-sram"
                #:args (ram-path)
                (modify-sram ram-path 1)))
