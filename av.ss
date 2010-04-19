#lang scheme
(require (planet murphy/amb/amb)
         scheme/set)

;;; Utils
(define (amb-list-ref l)
  (for/amb ([e (in-list l)]) e))

(define (iprintf n . args)
  (for ([i (in-range n)])
    (printf " "))
  (apply printf args))

(define symbol-length
  (compose string-length symbol->string))

(define (pad-right s i)
  (format "~a~a" s (make-string (- i (symbol-length s)) #\space)))

;;; Data structures & macros
(define-struct av (id inputs outputs end-points) #:prefab)
(define avs (make-hasheq))
(define-syntax-rule (define-av id (input ...) (output ...) (end-point ...))
  (begin
    (define id (make-av 'id '(input ...) '(output ...) (set 'end-point ...)))
    (hash-set! avs 'id id)))

(define-syntax-rule (connect [(end-point ...) (root ...)] ...)
  (display-config
   (connect* '[(end-point ...) (root ...)] ...)))

(define-syntax-rule (verify conns [(end-point ...) (root ...)] ...)
  (verify* 'conns '[(end-point ...) (root ...)] ...))

(define-struct connection (from output to) #:prefab)
(define-struct config (avs conns) #:prefab)
(define (init-config)
  (make-config 
   (for/fold ([ht (make-immutable-hasheq empty)])
     ([(k v) (in-hash avs)])
     (hash-set ht k v))
   empty))

(define (config-end-points c com)
  (av-end-points (hash-ref (config-avs c) com)))
(define (config-outputs c com)
  (av-outputs (hash-ref (config-avs c) com)))
(define (config-inputs c com)
  (av-inputs (hash-ref (config-avs c) com)))
(define (config-components c)
  (hash-map (config-avs c) (lambda (k v) k)))
(define (config-connections c from)
  (remove-duplicates
   (for/list ([conn (in-list (config-conns c))]
              #:when (symbol=? from (connection-from conn)))
     (connection-to conn))))
(define (remove-input c com in)
  (define avs (config-avs c))
  (define com-av (hash-ref avs com))
  (define new-av
    (struct-copy av com-av
                 [inputs (remq in (av-inputs com-av))]))
  (define new-avs (hash-set avs com new-av))
  (struct-copy config c [avs new-avs]))
(define (add-connection c conn)
  (struct-copy
   config c
   [conns (list* conn (config-conns c))]))
(define (duplicate-end-points c to from)
  (define avs (config-avs c))
  (define to-av (hash-ref avs to))
  (define new-to-av
    (struct-copy av to-av
                 [end-points 
                  (set-union (config-end-points c to)
                             (config-end-points c from))]))
  (define new-avs (hash-set avs to new-to-av))
  (struct-copy config c [avs new-avs]))

(define display-config
  (match-lambda
    [(struct config (_ conns))
     (define max-from
       (apply max (map (compose symbol-length connection-from) conns)))
     (define max-output
       (apply max (map (compose symbol-length connection-output) conns)))
     (for ([c (in-list conns)])
       (match-define (struct connection (from output to)) c)
       (printf "~a ~a to ~a~n" 
               (pad-right from max-from)
               (pad-right output max-output)
               to))]))

;;; Logic
(define (connect* . l)
  (call-with-amb-prompt
   (lambda ()
     (for/fold ([config (init-config)])
       ([es*rs (in-list l)])
       (match-define (list end-points roots) es*rs)
       (for/fold ([config config])
         ([r (in-list roots)])
         (define new-config
           (wire-to-end-points config r end-points))
         new-config)))
   (lambda ()
     "Cannot find a connection plan")))

(define (wire-to-end-points c root end-points)
  (for/fold ([c c])
    ([ep (in-list end-points)])
    #;(iprintf (length (config-conns c))
               "Goal: ~S -> ~S~n"
               root ep)
    (wire-to-end-point (set) c root ep)))

(define (wire-to-end-point seen c from goal)
  (amb
   ; If we are already connected, stop
   (let ()
     (amb-assert (set-member? (config-end-points c from) goal))
     c)
   
   ; Try to go through an existing connection
   (let ()
     (define to (amb-list-ref (config-connections c from)))
     ; Try to connect to to the end-point
     (define config-after-end-point
       (wire-to-end-point (set-add seen to) c to goal))
     ; Record that com is connected to all inter's end-points
     (duplicate-end-points config-after-end-point from to))
   
   ; Try to go through a new intermediary
   (let ()
     ; Choose a possible place to connect it to
     (define to (amb-list-ref (config-components c)))
     ; Assert that this is not a loop
     (define loop-assert
       (amb-assert (not (set-member? seen to))))
     ; Make the connection (fails if it isn't possible)
     (define config-after-conn (create-connection c from to))
     ; Try to connect that to the end-point
     (define config-after-end-point
       (wire-to-end-point (set-add seen to) config-after-conn to goal))
     ; Record that com is connected to all inter's end-points
     (duplicate-end-points config-after-end-point from to))))

(define (create-connection c from to)
  ; Choose a possible output
  (define output (amb-list-ref (config-outputs c from)))
  ; Make the connection from there
  (create-connection/output c from output to))

(define (create-connection/output c from output to)
  ; Assert that it is an open input
  (define open-assertion
    (amb-assert (member output (config-inputs c to))))
  #;(define _
      (iprintf (length (config-conns c))
               "Choice: ~S -> ~S via ~S~n"
               from to output))
  ; Update the configuration to remove the input and record the connection
  (define c-after-remove
    (remove-input c to output))
  (define c-after-conn
    (add-connection c-after-remove (make-connection from output to)))
  c-after-conn)

;;; Example

; Inputs
(define-av Wii () (Component-Video RCA) ())
(define-av PS3 () (HDMI-Audio HDMI-Video) ())
(define-av Xbox360 () (HDMI-Audio HDMI-Video) ())
(define-av PS2 () (Component-Video RCA) ())
(define-av Saturn () (Composite-Video S-Video RCA) ())
(define-av Dreamcast:VGA () (DC:VGA) ())
(define-av Dreamcast:S-Video () (DC:S-Video) ())
(define-av PC:HDMI () (HDMI-Audio HDMI-Video) ())
(define-av PC:VGA () (VGA) ())

; Intermediates
(define-av DC-VGA-Box:VGA
  (DC:VGA)
  (VGA Headphone)
  ())
(define-av DC-VGA-Box:S-Video
  (DC:S-Video)
  (S-Video Composite-Video RCA)
  ())
#;(define-av Headphone->RCA-cable
  (Headphone)
  (RCA)
  ())
#;(define-av RCA-Switch
  (RCA RCA RCA)
  (RCA)
  ())
#;(define-av SVideo-Switch
  (S-Video S-Video)
  (S-Video)
  ())
#;(define-av VGA-Switch
  (VGA VGA)
  (VGA)
  ())

; Receiver
(define-av Receiver:HT-CT500
  (RCA RCA CoaxAudioDigital DigitalMediaPort HDMI-Audio HDMI-Audio HDMI-Audio OpticalAudio OpticalAudio OpticalAudio)   
  ()
  (Sound))
(define-av VideoSwitch:HT-CT500
  (Component-Video Component-Video Composite-Video HDMI-Video HDMI-Video HDMI-Video)   
  (HDMI-Video)
  ())

; TV
#;(define-av TV:232T
  (HDMI-Video Component-Video VGA S-Video Composite-Video)
  ()
  (Video))
#;(define-av TVSpeakers:232T
    (HDMI-Audio RCA RCA RCA)
    ()
    (Sound))

; New TV
(define-av TV:Bravia:AudioSwitch
  (RCA RCA RCA Headphone HDMI-Audio HDMI-Audio HDMI-Audio HDMI-Audio)
  (OpticalAudio)
  ())
(define-av TV:Bravia
  (Component-Video Composite-Video Composite-Video HDMI-Video HDMI-Video HDMI-Video HDMI-Video VGA)
  ()
  (Video))

; The query
(connect 
 [(Video)
  (#;PC:VG)]
 [(Video Sound)
  (Saturn Dreamcast:VGA Dreamcast:S-Video Wii PS3 Xbox360 PS2 PC:HDMI)])