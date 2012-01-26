#lang racket/base
(require racket/list
         datalog)

(define ranking (make-theory))

;; Transitivity
(datalog!
 ranking
 (! (:- (<= A C)
        (<= A B)
        (<= B C))))

(define space
  '(smb1 smb2 smb3 ff4 ff6 ff7 ff13))

;; Reflexivity
(for
 ([x (in-list space)])
 (datalog!
  ranking
  (! (<= x x))))

;; Knowledge
(datalog!
 ranking
 (! (<= ff4 ff6))
 (! (<= ff7 ff6))
 (! (<= ff7 ff13))
 (! (<= smb1 smb2))
 (! (<= ff4 smb3))

 (! (<= smb2 smb3))
 (! (<= ff7 ff4))
 (! (<= ff13 ff6))
 (! (<= ff4 ff13))
 (! (<= smb2 ff7))
 (! (<= smb3 ff13)))

(define (lift-<= x y)
  (not
   (empty?
    (datalog ranking
             (? (<= x y))))))

(define (inspect-<= x y)
  (cond
   [(lift-<= x y)
    #t]
   ;; By anti-symmetry
   [(lift-<= y x)
    #f]
   [else
    (printf "Unknown: (<= ~a ~a)\n" x y)
    #f]))

(sort space inspect-<=)

(write-theory ranking)

