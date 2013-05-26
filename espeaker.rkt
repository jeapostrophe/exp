#lang racket/base
(require racket/gui/base
         racket/class)

(define (go!)
  (define-values (es-sp espeak-out espeak-in espeak-err)
    (subprocess (current-output-port) #f (current-error-port)
                "/usr/bin/espeak" "-x"))

  (define current "")

  (define es-frame%
    (class* frame% ()
      (define/override (on-subwindow-char r e)
        (define kc (send e get-key-code))
        (when (char? kc)
          (cond
            [(and (not (char=? kc #\return)) (not (char=? kc #\space)))
             (set! current (string-append current (string kc)))]
            [else
             (fprintf espeak-in "~a \n" current)
             (flush-output espeak-in)
             (set! current "")])
          (send mw set-status-text current))
        #t)
      (super-new)))

  (define mw
    (new es-frame% [label "espeaker"]
         [style '(no-resize-border
                  no-caption
                  hide-menu-bar
                  no-system-menu)]))

  (send mw create-status-line)
  (send mw show #t)
  (send mw focus))

(module+ main
  (go!))
