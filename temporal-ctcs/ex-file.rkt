#lang racket/load

(module files racket
  (require "temporal.rkt" unstable/match)
  (define (use-files f)
    (define (open i) (void))
    (define (close i) (void))
    (f open close))
  
  (define evts empty)
  (define (file-monitor evt)
    (set! evts (list* evt evts))
    (not
     (or
      ; By the time file-user returns, it must have closed everything it opens
      (match evts
        [(list (evt:return 'file-user _ _ app _ _)
               between-evts ...
               (evt:call 'file-user _ _ app _)
               _ ...)
         (define still-open
           (for/fold ([fds (set)])
             ; The log is stored in reverse, so we have to reverse it to look at the in temporal order
             ([evt (in-list (reverse between-evts))])
             (match evt
               [(evt:call 'open _ _ _ (list fd))
                (set-add fds fd)]
               [(evt:call 'close _ _ _ (list fd))
                (set-remove fds fd)]
               [_
                fds])))
         (not (set-empty? still-open))]
        ; If the above pattern doesn't match, then we haven't yet returned
        [_
         #f])
      ; We cannot close something that is not open...
      (match evts
        [(list (evt:call 'close _ _ _ (list fd))
               (and since-evts (not (evt:call 'file-user _ _ _ _))) ...
               (evt:call 'file-user _ _ _ _)
               _ ...)
         (define 
           fd-opened?
           (for/fold ([fd-opened? #f])
             ([evt (in-list (reverse since-evts))])
             (match evt
               [(evt:call 'open _ _ _ (list (== fd)))
                #t]
               [(evt:call 'close _ _ _ (list (== fd)))
                #f]
               [_
                fd-opened?])))
         (not fd-opened?)]
        [_
         #f]))))
  
  (provide/contract
   [use-files
    (->t file-monitor 'use-files
         (->t file-monitor 'file-user
              (->t file-monitor 'open
                   any/c any/c)
              (->t file-monitor 'close
                   any/c any/c)
              any/c)
         any/c)]))

(module good-client racket
  (require 'files)
  (define (go!)
    (use-files
     (λ (open close)
       (open 0)
       (close 0)
       (open 0)
       (open 1)
       (close 0)
       (close 1)
       (open 2)
       (open 1)
       (close 1)
       (close 2))))
  (provide go!))

(module bad-client1 racket
  (require 'files)
  (define (go!)
    (use-files
     (λ (open close)
       (open 0))))
  (provide go!))
(module bad-client2 racket
  (require 'files)
  (define (go!)
    (use-files
     (λ (open close)
       (close 0))))
  (provide go!))
(module bad-client3 racket
  (require 'files)
  (define (go!)
    (use-files
     (λ (open close)
       (open 0)
       (close 0)
       (close 0))))
  (provide go!))

(module tester racket
  (require tests/eli-tester
           (prefix-in good: 'good-client)
           (prefix-in bad1: 'bad-client1)
           (prefix-in bad2: 'bad-client2)
           (prefix-in bad3: 'bad-client3))
  (test
   (good:go!) => (void)
   (bad1:go!) =error> "disallowed"
   (bad2:go!) =error> "disallowed"
   (bad3:go!) =error> "disallowed"))

(require 'tester)
       