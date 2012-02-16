(defun je/games/key ()
  "Key extraction function"
  (list
   ;; 0
   (if (looking-at org-complex-heading-regexp)
       (match-string 4)
     nil)
   ;; 1
   (org-entry-get nil "Year")
   ;; 2
   (org-entry-get nil "Completed")
   ;; 3
   (org-entry-get nil "PlayAgain")
   ;; 4
   (org-entry-get nil "Reviewed")))
(defun je/games/compare (x y)
  "Comparsion function"
  (let ((x-name (nth 0 x))
        (x-year (nth 1 x))
        (x-completed (nth 2 x))
        (x-play-again (nth 3 x))
        (x-reviewed (nth 4 x))
        (y-name (nth 0 y))
        (y-year (nth 1 y))
        (y-completed (nth 2 y))
        (y-play-again (nth 3 y))
        (y-reviewed (nth 4 y)))    
    (cond
     ;; Active is first
     ((and (string= x-completed "Active")
           (not (string= x-completed y-completed)))
      t)
     ((and (string= y-completed "Active")
           (not (string= x-completed y-completed)))
      nil)
     ;; Scheduled next
     ((and (string= x-completed "Scheduled")
           (not (string= x-completed y-completed)))
      t)
     ((and (string= y-completed "Scheduled")
           (not (string= x-completed y-completed)))
      nil)
     ;; Queue next
     ((and (string= x-completed "Queue")
           (not (string= x-completed y-completed)))
      t)
     ((and (string= y-completed "Queue")
           (not (string= x-completed y-completed)))
      nil)
     ;; Not reviewed (i.e. is N) is first.
     ((and (stringp x-reviewed) (string= x-reviewed "N")
           (not (string= x-reviewed y-reviewed)))
      t)
     ((and (stringp y-reviewed) (string= y-reviewed "N")
           (not (string= x-reviewed y-reviewed)))
      nil)
     ;; Don't play again is last
     ((and (stringp x-play-again)
           (string-match "N" x-play-again)
           (not (string= x-play-again y-play-again)))
      nil)
     ((and (stringp y-play-again)
           (string-match "N" y-play-again)
           (not (string= x-play-again y-play-again)))
      t)     
     ;; Completed is last
     ((and (stringp x-completed)
           (string-match "Y" x-completed)
           (not (string= x-completed y-completed)))
      nil)
     ((and (stringp y-completed)
           (string-match "Y" y-completed)
           (not (string= x-completed y-completed)))
      t)
     ;; Sort by year
     ((and (stringp x-year) (stringp y-year) (not (string= x-year y-year)))
      (string< x-year y-year))
     ;; Sort by name
     (t
      (string< x-name y-name)))))
(defun je/games/sort ()
  "Sort my games database"
  (interactive)

  (save-excursion
    (org-columns-quit)
    ;; Goto the top of the buffer
    (goto-char (point-min))
    ;; Sort
    (org-sort-entries nil ?f 'je/games/key 'je/games/compare)
    (save-buffer)
    (org-cycle)
    (org-cycle)
    (org-columns)))
