#lang scheme

; Structures
(define-struct abs (str con dex int wis cha) #:prefab)

(define-struct char (name level xp
                          alignment deity
                          abs-base abs-choice
                          race race-options
                          class class-options
                          ; paragon
                          ; epic
                          feats
                          powers
                          wealth
                          armor shield melee-weapon missile-weapon
                          items))

; Operations
(define (ab-modifier v)
  (quotient (- v 10) 2))

(define (effective-abs c)
  (define lvl (char-level c))
  (define init (char-abs-base c))
  (define post-race
    (case (char-race c)
      [(Elf) (struct-copy abs init
                          [dex (+ 2 (abs-dex init))]
                          [wis (+ 2 (abs-wis init))])]
      [else 
       (error 'effective-abs "Unknown race: ~a" (char-race c))]))
  (define post-paragon
    (if (lvl . >= . 11)
        (struct-copy abs post-race
                     [str (+ 1 (abs-str post-race))]
                     [con (+ 1 (abs-con post-race))]
                     [dex (+ 1 (abs-dex post-race))]
                     [int (+ 1 (abs-int post-race))]
                     [wis (+ 1 (abs-wis post-race))]
                     [cha (+ 1 (abs-cha post-race))])
        post-race))
  (define post-epic
    (if (lvl . >= . 21)
        (struct-copy abs post-paragon
                     [str (+ 1 (abs-str post-paragon))]
                     [con (+ 1 (abs-con post-paragon))]
                     [dex (+ 1 (abs-dex post-paragon))]
                     [int (+ 1 (abs-int post-paragon))]
                     [wis (+ 1 (abs-wis post-paragon))]
                     [cha (+ 1 (abs-cha post-paragon))])
        post-paragon))
  (for*/fold ([the-abs post-epic])
             ([ab-ch (in-vector (char-abs-choice c))]
              #:when (lvl . >= . (vector-ref ab-ch 0))
              [ab (in-list (vector-ref ab-ch 1))])
     (case ab
       [(Str) (struct-copy abs the-abs
                           [str (+ 1 (abs-str the-abs))])]
       [(Con) (struct-copy abs the-abs
                           [con (+ 1 (abs-con the-abs))])]
       [(Dex) (struct-copy abs the-abs
                           [dex (+ 1 (abs-dex the-abs))])]
       [else
        (error 'effective-abs "Unknown attribute: ~a" ab)])))

; Kugo
(define Kugo-Zale
  (make-char 
   "Kugo Zale"
   
   1 0
   'Good 'Avandra
   
   #s(abs 18 10 14 8 13 10)
   #(#( 4 (Str Con))
     #( 8 (Str Con))
     #(14 (Str Dex))
     #(18 (Str Dex))
     #(24 (Str Con))
     #(28 (Str Con)))
   
   'Elf 
   empty 
   
   'Fighter
   '((Skills (Endurance Intimidate Streetwise))
     One-handed)
      
   '(Toughness)
   (list empty ;At-will
         empty ;Utility
         empty ;Encounter
         empty) ;Daily
   100
   'Scale 'Heavy 'Spear 'Javelin
   empty))