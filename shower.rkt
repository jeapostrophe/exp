#lang racket/base
(require racket/system
         racket/file)

(define steps
  (list "Wet body"
        #"Wet hair"
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
        "Rinse loufa"
        #"Rinse head"
        "Wet face cloth"
        "Wash face"
        "Rinse face cloth"
        "Rinse body"))

(define unit-len 5.0)

(/ (* unit-len (length steps)) 60.0)

(define tmp-dir (make-temporary-file "~a" 'directory))

(parameterize ([current-directory tmp-dir])
  (for ([step-name (in-list steps)]
        [i (in-naturals)])
    (define step-name-str
      (if (string? step-name)
        step-name
        (bytes->string/utf-8 step-name)))
    (define step-announce-wav (format "~a-announce.wav" i))
    (system (format "espeak -w ~a ~s" step-announce-wav step-name-str))
    (system (format "play ~a" step-announce-wav))))

(delete-directory/files tmp-dir)
