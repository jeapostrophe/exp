#lang racket
(require (planet neil/csv))

(match-define (list-rest header games)
              (csv->list (current-input-port)))

(define (extend-l l)
  (append l (build-list (- (length header) (length l)) (λ (i) ""))))

(define (mprintf fmt arg)
  (unless (string=? "" arg)
          (printf fmt arg)))

(printf "* Games\n")
(for ([entry (in-list games)])
     (match-define (list system year game/en game/jp can-play? last-price paid recv done? comments again? blog?) (extend-l entry))
     (printf "** ~a\n" game/en)
     (printf "  :PROPERTIES:\n")
     (mprintf "  :System:\t~a\n" system)
     (mprintf "  :Year:\t~a\n" year)
     (mprintf "  :Completed:\t~a\n" done?)
     (mprintf "  :PlayAgain:\t~a\n" again?)
     (mprintf "  :Reviewed:\t~a\n" blog?)
     (printf "  :END:\n")
     (mprintf "\n  ~a\n\n" comments))
(printf #<<END
* Settings
#+COLUMNS: %25ITEM %System %Year %Completed %PlayAgain %Reviewed

END
)
