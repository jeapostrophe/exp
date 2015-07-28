(defun faker-start ()
  "start faking the writing of a file"
  (interactive)
  (let* ((fn (read-file-name "Real file: "))
         (bufn (generate-new-buffer-name " faker"))
         (buf (get-buffer-create bufn)))
    (message "faking with fn")
    (with-current-buffer buf
      (insert-file-contents fn))
    (faker-loop buf)))

(defun faker-loop (buf)
  (message "faker loop")
  (message (read-event))
  (message (read-event))
  (message (read-event))
  (message (read-event))
  (message (read-event)))





