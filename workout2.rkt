#lang at-exp racket/base
(require racket/path
         racket/match
         xml)

(define warmup
  (list "3 Plane Neck Movement"
        "Finger Flexion/Extension"
        "Wrist Circles"
        "Elbow Circles"
        "Large Arm Circles"
        "Circular Shrugs"
        "Torso Twists"
        "Side Bends"
        "Forward/Back Bends"
        "Pelvic Tilts"
        "Hula-hoop Hip Circles"
        "Leg Rotations"
        "High Knee Raises"
        "Kick Backs / Butt Kicks"
        "Ankle Circles"
        "Ankle Tilts"
        "Toe Flexion / Extension"
        "Wall Extensions"
        "Band Stretches"
        "Bar Dislocates"
        "Cat/Cow Bends"
        "Calf Stretch"
        "Knee to Wall"
        "Front Leg Swings"
        "Side Leg Swings"
        "Ring Sphinx"
        "Wrist Warmup"
        "Deep Squat Arm Raise"
        "Passive Hang"
        "Knee to Chest Lying Down"
        "Pretzel Twist"))

(define exercises
  `(;; A
    (["Squat" "squat"]
     ["Bench Press" "bench"]
     ["Barbell Row" "barbell-row"]
     ["Dips" #f]
     ["Planks" #f]
     ["Barbell Hip Thrust" #f]
     ["Pushups" #f])
    ;; B
    (["Squat" "squat"]
     ["Overhead Press" "overhead-press"]
     ["Deadlift" "deadlift"]
     ["Chinups" #f]
     ["Hanging Knee Raises" #f]
     ["Barbell Hip Thrust" #f]
     ["Pullups" #f])))

(define GROUPS '())
(define (group-menu)
  `(div ([class "menu"])
        (ul
         ,@(for/list ([g (in-list (reverse GROUPS))])
             (match-define (cons id label) g)
             `(li (button ([onclick ,(format "swap(~v);" id)]) ,label))))))
(define (group label . body)
  (define id (symbol->string (gensym)))
  (set! GROUPS (cons (cons id label) GROUPS))
  `(div ([class "group"]
         [id ,id]
         [style "display: none;"])
        (h1 ,label)
        ,@body))

(define imgs
  (build-path (find-system-path 'home-dir) "Downloads"
              "Exercise" "StrongLifts" "imgs"))
(define sorted-imgs
  (sort (directory-list imgs) string<=? #:key path->string))
(define (help label key)
  (group
   label
   `(div ([class "help"])
         ,@(for/list ([p sorted-imgs]
                      #:when (regexp-match (regexp-quote key) p))
             `(img ([src ,(format "workout2-imgs/~a" (file-name-from-path p))]) " ")))))

(define (generate!)
  (define gs
    (reverse
     (list
      (group
       "Warmup"
       `(ol
         ,@(for/list ([w (in-list warmup)])
             `(li ,w))))
      (group
       "Workouts"
       `(table
         (tr (td "A") (td "B"))
         (tr (td ([colspan "2"])
                 "Squat (5x5)"))
         (tr (td "Bench Press (5x5)")
             (td "Overhead Press (5x5)"))
         (tr (td "Barbell Row (5x5)")
             (td "Deadlift (1x5)"))
         (tr (td "Dips (3x10)")
             (td "Chinups (3x10)"))
         (tr (td "Planks (6x60s)")
             (td "Hanging Knee Raise (3x8)"))
         (tr (td ([colspan "2"])
                 "Barbell Hip Thrust (3x10)"))
         (tr (td "Pullups (reps)")
             (td "Pushups (reps)"))))
      (help "Squat" "squat")
      (help "Bench Press" "bench")
      (help "Barbell Row" "barbell-row")
      (help "Overhead Press" "overhead-press")
      (help "Deadlift" "deadlift")
      (group-menu))))
  (write-xexpr
   `(html
     (head (title "Workout")
           (link ([rel "stylesheet"] [href "workout2.css"]) "")
           (script
            ,(make-cdata
              #f #f
              @string-append{
function swap(which) {
 console.log(which)@";"
 var divsToHide = document.getElementsByClassName("group");
 for( var i = 0@";" i < divsToHide.length@";" i++) {
  divsToHide[i].style.display = "none"@";" }
 document.getElementById(which).style.display = "block"@";" } })))
     (body
      ,@gs))))

(module+ main
  ;; racket -t workout2.rkt && rsync -aL --progress workout2* uml:public_html/w/
  (require racket/runtime-path)
  (define-runtime-path dest "workout2.html")
  (with-output-to-file dest
    #:exists 'replace
    generate!))
