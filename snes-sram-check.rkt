#lang racket

#|
I looked at the source of bsnes's cartridge.hpp to figure this out.
|#

(define << arithmetic-shift)
(define & bitwise-and)
(define ~ bitwise-not)
(define-syntax-rule (&& a b) (and a b))
(define == =)
(define (!= a b) (not (= a b)))

(define (read-uint8@ pth addr)
  (define b
    (with-input-from-file pth
      (λ ()
        (file-position (current-input-port) addr)
        (read-byte))))
  (if (eof-object? b)
      0
      b))

(define CartName    #x00)
(define Mapper      #x15)
(define RomType     #x16)
(define RomSize     #x17)
(define RamSize     #x18)
(define CartRegion  #x19)
(define Company     #x1a)
(define Version     #x1b)
(define Complement  #x1c);  //inverse checksum
(define Checksum    #x1e)
(define ResetVector #x3c)

(define lo-header #x007fc0)
(define hi-header #x00ffc0)
(define ex-header #x40ffc0)

(define-syntax-rule (+= id e)
  (set! id (+ id e)))
(define-syntax-rule (-= id e)
  (set! id (- id e)))
(define-syntax-rule (++ id) (+= id 1))

(define (find-header r-p)
  (define score-lo (score-header r-p lo-header))
  (define score-hi (score-header r-p hi-header))
  (define score-ex (score-header r-p ex-header))
  (unless (zero? score-ex) (+= score-ex 4)) ; favor ExHiROM on images > 32mbits
  
  (cond
    [(and (score-lo . >= . score-hi)
          (score-lo . >= . score-ex))
     lo-header]
    [(score-hi . >= . score-ex)
     hi-header]
    [else
     ex-header]))

(define (score-header r-p addr)
  (define (data a) (read-uint8@ r-p a))
  (let/ec return
    (define size (file-size r-p))
    (when (size . < . (addr . + . 64)) (return 0)) ; image too small to contain header at this location?
    (define score 0)
    
    (define resetvector (bitwise-ior (data (+ addr ResetVector)) ((data (+ addr (ResetVector . + . 1))) . << . 8)))
    (define checksum (bitwise-ior (data (+ addr Checksum)) ((data (+ addr (Checksum . + . 1))) . << . 8)))
    (define complement (bitwise-ior (data (+ addr Complement)) ((data (+ addr (Complement . + . 1))) . << . 8)))
    
    ;  first opcode executed upon reset
    (define resetop (data (bitwise-ior (addr . & . (~ #x7fff))
                                       (resetvector . & . #x7fff))))
    ; mask off irrelevent FastROM-capable bit
    (define mapper ((data (addr . + . Mapper)) . & . (~ #x10)))
    
    ;$00:[000-7fff] contains uninitialized RAM and MMIO.
    ;reset vector must point to ROM at $00:[8000-ffff] to be considered valid.
    (when (resetvector . < . #x8000) (return 0))
    
    ;//some images duplicate the header in multiple locations, and others have completely
    ;//invalid header information that cannot be relied upon.
    ;//below code will analyze the first opcode executed at the specified reset vector to
    ;//determine the probability that this is the correct header.
    
    (define-syntax-rule (resetop-is e ...)
      (or (= resetop e) ...))
    
    ;//most likely opcodes
    (when (resetop-is #x78 ;  //sei
                      #x18 ;  //clc (clc; xce)
                      #x38 ; //sec (sec; xce)
                      #x9c ; //stz $nnnn (stz $4200)
                      #x4c ; //jmp $nnnn
                      #x5c ; //jml $nnnnnn
                      ) 
      (score . += . 8))
    
    ;//plausible opcodes
    (when (resetop-is #xc2 ; //rep #$nn
                      #xe2 ; //sep #$nn
                      #xad ; //lda $nnnn
                      #xae ; //ldx $nnnn
                      #xac ; //ldy $nnnn
                      #xaf ; //lda $nnnnnn
                      #xa9 ; //lda #$nn
                      #xa2 ; //ldx #$nn
                      #xa0 ; //ldy #$nn
                      #x20 ; //jsr $nnnn
                      #x22 ; //jsl $nnnnnn
                      ) 
      (score . += . 4))
    
    ;//implausible opcodes
    (when (resetop-is #x40 ; //rti
                      #x60 ; //rts
                      #x6b ; //rtl
                      #xcd ; //cmp $nnnn
                      #xec ; //cpx $nnnn
                      #xcc ; //cpy $nnnn
                      ) 
      (score . -= . 4))
    
    ;//least likely opcodes
    (when (resetop-is #x00 ; //brk #$nn
                      #x02 ; //cop #$nn
                      #xdb ; //stp
                      #x42 ; //wdm
                      #xff ; //sbc $nnnnnn,x
                      ) 
      (score . -= . 8))
    
    ;//at times, both the header and reset vector's first opcode will match ...
    ;//fallback and rely on info validity in these cases to determine more likely header.
    
    ;//a valid checksum is the biggest indicator of a valid header.
    (when ((((checksum . + . complement) . == . #xffff) . && . (checksum . != . 0)) . && . (complement . != . 0)) (score . += . 4))
    
    (when ((addr . == . lo-header) . && . (mapper . == . #x20)) (score . += . 2));  //0x20 is usually LoROM
    (when ((addr . == . hi-header) . && . (mapper . == . #x21)) (score . += . 2));  //0x21 is usually HiROM
    (when ((addr . == . lo-header) . && . (mapper . == . #x22)) (score . += . 2));  //0x22 is usually ExLoROM
    (when ((addr . == . ex-header) . && . (mapper . == . #x25)) (score . += . 2));  //0x25 is usually ExHiROM
    
    (when ((data[addr . + . Company]) . == . #x33) (score . += . 2));        //0x33 indicates extended header
    (when ((data[addr . + . RomType]) . < . #x08) (++ score))
    (when ((data[addr . + . RomSize]) . < . #x10) (++ score))
    (when ((data[addr . + . RamSize]) . < . #x08) (++ score))
    (when ((data[addr . + . CartRegion]) . < . 14) (++ score))
    
    (when (score . < . 0) (set! score 0))
    (return score)))

(for ([r-p (in-list (directory-list))])
  (define r-s (path->string r-p))
  (when (regexp-match #rx"smc$" r-s)
    (define header-start (find-header r-p))
    (define ram-size
      (<<
       1024
       (& (read-uint8@ 
           r-p
           (+ header-start
              RamSize))
          7)))
    (when (= ram-size 1024)
      (set! ram-size 0))
    
    (unless (zero? ram-size)
      (define s-s (format "~asrm" (substring r-s 0 (- (string-length r-s) 3))))
      (with-output-to-file s-s
        (λ ()
          (for ([i (in-range (* 8 1024))]) (write-byte 0))
          (flush-output))))))