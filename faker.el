(defun faker-start ()
  "start faking the writing of a file"
  (interactive)
  (let ((fn (read-file-name "Real file: ")))
    (message "faking with fn")
    (faker-loop fn)))

(defun faker-loop (fn)
  (message "faker loop")
  (read-event))

