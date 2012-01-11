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
    ;; I would like everything that has not been reviewed (i.e. is N) to
    ;; be first.
    (cond
     ((and (equal x-reviewed "N")
           (not (equal x-reviewed y-reviewed)))
      t)
     (t
      nil))))
(defun je/games/sort ()
  "Sort my games database"
  (interactive)

  (save-excursion
    (org-columns-remove-overlays)
    ;; Goto the top of the buffer
    (goto-char (point-min))
    ;; Sort
    (org-sort-entries nil ?f 'je/games/key 'je/games/compare)
    (save-buffer)
    (org-cycle)
    (org-cycle)
    (org-columns)))
