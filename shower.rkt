#lang racket/base
(require racket/system
         racket/port
         racket/list
         racket/file)

(define steps
  (list #"Wet hair"
        "Wet body"        
        #"Get shampoo"
        #"Shampoo head"
        #"Rinse head"
        #"Get conditioner"
        #"Condition head"
        "Wet loufa"
        "Put soap on loufa"
        "Lather loufa"
        "Wash left arm"
        "Wash right arm"
        "Wash torso"
        "Wash right leg"
        "Wash left leg"
        "Wash back"
        #"Rinse head"
        "Rinse loufa"
        "Rinse body"))

;; (I think I actually count about 9 seconds when I try to count 5)
(define unit-len 10.0)

(define (system+ s)
  (eprintf "~a\n" s)
  (system s))

(module+ main
  (define music-dir "/home/jay/Downloads/shower/MegaMan2")
  (define shower-wav "/home/jay/Downloads/shower/shower.wav")
  (define shower-mp3 "/home/jay/Downloads/shower/shower.mp3")
  (define shower/hair-wav "/home/jay/Downloads/shower/shower-hair.wav")
  (define shower/hair-mp3 "/home/jay/Downloads/shower/shower-hair.mp3")
  (define alarm-sound "/home/jay/Downloads/shower/alarm.aif")
  (define tmp-dir (make-temporary-file "~a" 'directory))

  (parameterize ([current-directory tmp-dir])
    (define wavs
      (for/list ([step-name (in-list steps)]
                 [music-name
                  (in-cycle (in-list (sort (directory-list music-dir)
                                           string-ci<=?
                                           #:key path->string)))]
                 [i (in-naturals)])
        (define music (path->string (build-path music-dir music-name)))
        (define hair?
          (not (string? step-name)))
        (define step-name-str
          (if (string? step-name)
            step-name
            (bytes->string/utf-8 step-name)))
        (define step-announce-wav/mono (format "~a-announce-mono.wav" i))
        (system+ (format "espeak -k20 -w ~a ~s" step-announce-wav/mono step-name-str))
        (define step-announce-wav (format "~a-announce.wav" i))
        (system+ (format "sox -v 2.0 ~a -c 2 -r 44100 ~a"
                         step-announce-wav/mono
                         step-announce-wav))
        (define announce-len-str
          (regexp-replace*
           #rx"\n"
           (with-output-to-string
             (λ ()
               (system+ (format "soxi -D ~a" step-announce-wav))))
           ""))
        (define announce-len
          (string->number announce-len-str))
        (define music-len
          (- unit-len announce-len))
        (define step-music-wav
          (format "~a-music.wav" i))

        (system+ (format "sox ~s ~s trim 0 ~a"
                         music step-music-wav music-len))
        (list hair? step-announce-wav step-music-wav)))

    (define (combine wavs shower-wav shower-mp3)
      (system+
       (format "sox -v 4.0 ~a ~a ~a"
               (apply string-append (add-between (apply append wavs) " "))
               alarm-sound
               shower-wav))
      (system+ (format "lame -S ~a ~a" shower-wav shower-mp3)))

    (combine (filter-map (λ (l) (and (not (first l))
                                     (rest l)))
                         wavs)
             shower-wav shower-mp3)
    (combine (map rest wavs) shower/hair-wav shower/hair-mp3))

  (delete-directory/files tmp-dir))
