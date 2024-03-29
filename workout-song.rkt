#lang racket/base
(require racket/system
         racket/port
         racket/path
         racket/list
         racket/file
         racket/match)

(struct music (label))
(struct action (len s))

(define (+rest len)
  (action len "Take A Rest"))
(define (action+rest len s)
  (list (action len s)
        (+rest (max 5 (* len 2/10)))))
;; XXX Add count to know when last one is
(define (repeat x l)
  (make-list x l))

(define PLAN
  (flatten
   (list
    (music "action")
    (action 30 "Arm Swing")
    (action 15 "Shoulder Rotate Left Forward")
    (action 15 "Shoulder Rotate Left Backward")
    (action 15 "Shoulder Rotate Right Forward")
    (action 15 "Shoulder Rotate Right Backward")

    (action 0 "Get Ready")
    (repeat 4 (action+rest 30 "Hindu Squat"))

    (action 3 "Switch Positions")
    (action+rest 60 "Bridge")
    (repeat 12 (action+rest 20 "Crunches"))

    (action 3 "Get Ready")
    (action 120 "Bridge") (+rest 6)
    (action 60 "Full Plank") (+rest 6)
    (action 30 "Elbow Plank") (+rest 3)
    (action 30 "Side Plank Left") (+rest 3)
    (action 30 "Side Plank Right") (+rest 3)
    (action 30 "Raised Plank Left") (+rest 3)
    (action 30 "Raised Plank Right") (+rest 3)
    (action 30 "Full Plank") (+rest 3)
    (action 60 "Elbow Plank") (+rest 6)

    (action 0 "Switch Positions")
    (action+rest 60 "Bridge")
    (repeat 12 (action+rest 20 "Push Ups"))

    (action 3 "Time to Stretch")

    ;; XXX Doesn't start again at time 0
    (music "soft")
    (action 30 "Runner's Lunge Left")
    (action 30 "Runner's Lunge Right")
    (action 30 "Bicep Stretch")
    (action 30 "Head to Knee Stretch Left")
    (action 30 "Head to Knee Stretch Right")
    (action 30 "Neck Stretch Left")
    (action 30 "Neck Stretch Right")
    (action 30 "Shoulder Stretch Left")
    (action 30 "Shoulder Stretch Right")

    (music "meditate")
    (action (* 60 5) "Seated Meditation")

    (action 0 "You Did It"))))

(define LIFT-PLAN
  ;; 1:00 quad extension
  ;; 1:15 leg curl
  ;; 1:10 lat pull
  ;; 3:00 chest press
  ;; 1:00 shoulder press
  ;; 2:00 squat + calf raise
  ;; 1:00 shrugg
  ;; 0:30 arm curl (x25) and row (x25) (x4)
  ;; 1:00 tricep press
  ;;
  ;; 0:05 to 0:10 for moving things and resting
  #f)

(define dry? #f)

;;; Library

(define (delete-file* p)
  (unless dry?
    (delete-file p)))

(define (snoc l x)
  (append l (list x)))

(define (system+ . s)
  (eprintf "~v\n" s)
  (unless dry?
    (apply system* s)))

(define (audio-length p)
  (string->number
   (regexp-replace*
    #rx"\n"
    (with-output-to-string
      (λ ()
        (system* (find-executable-path "soxi") "-D" p)))
    "")))

(define (audio-announce! s dest)
  (define dest-mono
    (build-path (path-only dest) "dest-mono.wav"))
  (system+ (find-executable-path "espeak")
           "-k20" "-w" dest-mono
           s)
  (system+ (find-executable-path "sox")
           "--volume" "4" dest-mono  "-c" "2" "-r" "44100"
           dest)
  (delete-file* dest-mono)
  dest)

(define (audio-clip! src start end dest)
  (system+ (find-executable-path "sox")
           src "-r" "44100" dest
           "trim" (number->string start)
           (format "=~a" (number->string end)))
  dest)

(define (combine! wavs dest)
  (when (empty? wavs)
    (error 'combine "Cannot combine no wavs"))
  (apply system+
         (find-executable-path "sox")
         (append wavs (list dest)))
  (for-each delete-file* wavs)
  dest)

(define (wav->mp3! wav mp3)
  (system+ (find-executable-path "lame") "--preset" "medium" "-S" wav mp3)
  (delete-file* wav)
  mp3)

(define (display-len lab l)
  (local-require
   (prefix-in g:
              (combine-in gregor
                          gregor/period
                          gregor/time)))
  (printf "Total ~alength is: ~a\n"
          lab
          (g:+time-period (g:time 0) (g:seconds (inexact->exact (floor l))))))

(define (output! PLAN dir)
  (define tmp-dir (build-path dir "tmp"))
  (make-directory* tmp-dir)
  (define (tmp-p p)
    (build-path tmp-dir (format "~a.wav" p)))

  (define top-music-dir (build-path dir "music"))

  (define-values
    (total-len last-len wavs music!)
    (for/fold ([start-len 0]
               [last-len 0]
               [wavs '()]
               [music! void])
              ([p (in-list PLAN)]
               [i (in-naturals)])
      (match p
        [(music kind)
         (define music-dir
           (build-path top-music-dir kind))
         (define music-files
           (shuffle
            (filter (λ (x) (not (regexp-match #rx"DS_Store" x)))
                    (directory-list music-dir))))
         (struct music-info (path len))
         (define-values
           (total-music-len music-infos)
           (for/fold ([tot-len 0] [mis '()]) ([mf (in-list music-files)])
             (define p (build-path music-dir mf))
             (define len (audio-length p))
             (values (+ tot-len len)
                     (snoc mis (music-info p len)))))

         (display-len "(last music) " (- start-len last-len))
         (display-len (format "music (~a) " kind) total-music-len)

         (define (music! dest start end)
           (define-values (now wavs)
             (for/fold ([then 0]
                        [wavs '()])
                       ([mi (in-cycle music-infos)]
                        [i (in-naturals)]
                        #:break (< end then))
               (match-define (music-info p l) mi)
               (define now (+ then l))
               (define this-start (max start then))
               (define this-end (min end now))
               (define this-len (- this-end this-start))
               (define c-start (- this-start then))
               (define c-end (- this-end then))
               (when #t
                 (eprintf "~v\n"
                          (vector 'music!
                                  'start start 'end end
                                  'then then 'now now
                                  'tstart this-start 'tend this-end
                                  'cstart c-start 'cend c-end
                                  'len this-len)))
               (values now
                       (if (< 0 this-len)
                           (snoc wavs
                                 (audio-clip! p c-start c-end
                                              (tmp-p (format "~a-m" i))))
                           wavs))))
           (combine! wavs dest))
         (values start-len start-len wavs music!)]
        [(action 0 s)
         (define ann-wav
           (audio-announce! s (tmp-p (format "~a-ann" i))))
         (values start-len last-len (snoc wavs ann-wav) music!)]
        [(action this-len s)
         (define ann-wav
           (audio-announce! s (tmp-p (format "~a-ann" i))))
         (define end-len (+ start-len this-len))
         (define music-wav
           (music! (tmp-p (format "~a-mus" i)) start-len end-len))
         (define full-wav
           (combine! (list ann-wav music-wav) (tmp-p (format "~a-full" i))))
         (values end-len last-len (snoc wavs full-wav) music!)])))

  (display-len "(last music) " (- total-len last-len))

  (define dest-wav
    (combine! wavs (build-path dir "dest.wav")))
  (define dest-mp3
    (wav->mp3! dest-wav (build-path dir "dest.mp3")))

  (display-len "" total-len))

(define (go! dir)
  (output! PLAN dir))

(module+ main
  (require racket/cmdline)
  (command-line #:program "workout-song"
                #:args (dir) (go! dir)))
