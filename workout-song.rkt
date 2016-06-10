#lang racket/base
(require racket/system
         racket/port
         racket/list
         racket/file)

(define PLAN
  `())

(define (system+ . s)
  (eprintf "~v\n" s)
  (apply system* s))

(define (audio-length p)
  (string->number
   (regexp-replace*
    #rx"\n"
    (with-output-to-string
      (λ ()
        (system+ (find-executable-path "soxi") "-D" p)))
    "")))

(define (audio-announce! s dest)
  (define dest-mono
    (build-path (path-only dest) "dest-mono.wav"))
  (system+ (find-executable-path "espeak")
           "-k20" "-w" dest/mono
           s)
  (system+ (find-executable-path "espeak")
           "-v" "2.0" dest/mono
           "-c" "2" "-r" "44100"
           dest)
  (system+ (find-executable-path "rm")
           "-f"
           dest-mono))

(define (audio-clip! src start end dest)
  (system+ (find-executable-path "sox")
           src dest "trim" start end))

(define (combine! wavs dest-wav dest-mp3)
  (apply system+
         (find-executable-path "sox")
         "-v" "4.0"
         (append wavs (list dest-wav)))
  (system+ (find-executable-path "lame") "-S" dest-wav dest-mp3))

(define (output! PLAN dir)
  (define tmp-dir (build-path dir "tmp"))
  (make-directory* tmp-dir)
  
  (define music-dir (build-path dir "music"))
  (define music-files
    (sort (directory-list music-dir)
          string-ci<=?
          #:key path->string))
  (struct music-info (path len))
  (define music-infos
    (for/list ([mf (in-list music-files)])
      (define p (build-path music-dir mf))
      (define len (audio-length p))
      (music-info p len)))

  (define-values
    (music-len wavs)
    (for/fold ([start-len 0]
               [wavs '()])
              ([p (in-list PLAN)]
               [i (in-naturals)])
      (define end-len (+ music-len this-len))
      (define dest (build-path tmp-dir (format "~a.wav") i))
      (audio-announce! s dest)
      (values end-len
              (list* dest
                     wavs))))

  (define dest-wav (build-path dir "dest.wav"))
  (define dest-mp3 (build-path dir "dest.mp3"))
  (combine! (flatten wavs) dest-wav dest-mp3))

(define (go! dir)
  (output! PLAN dir))

(module+ main
  (require racket/cmdline)
  (command-line #:program "workout-song"
                #:args (dir) (go! dir)))

(module+ meh
    (define wavs
      (for/list ([step-name (in-list '())]
                 [music-name (in-list '())]
                 [i (in-naturals)])
        (define music (path->string (build-path music-dir music-name)))
        
        (define announce-len
          (audio-len step-announce-wav))
        (define music-len
          (- unit-len announce-len))
        (define step-music-wav
          (format "~a-music.wav" i))

        (system+ (format "sox ~s ~s trim 0 ~a"
                         music step-music-wav music-len))
        (list step-announce-wav step-music-wav))))
