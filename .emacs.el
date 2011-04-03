(defun run-current-file ()
  "Execute or compile the current file."
(interactive)
  (let (suffixMap fname suffix progName cmdStr)

    ;; a keyed list of file suffix to comand-line program path/name
    (setq suffixMap 
          '(("java" . "javai")))

    (save-buffer)

    (setq fname (buffer-file-name))
    (setq suffix (file-name-extension fname))
    (setq progName (cdr (assoc suffix suffixMap)))
    (setq cmdStr (concat progName " \""   fname "\" &"))

    (if (string-equal suffix "el") ; special case for emacs lisp
        (load-file fname) 
      (if progName
        (progn
          (message "Running...")
          (shell-command cmdStr "*run-current-file*"))
	(progn
	  (message "No recognized program file suffix for this file."))))))

(global-set-key (kbd "C-t") 'run-current-file)

(setq ansi-color-names-vector ; better contrast colors
      ["black" "red4" "green4" "yellow4"
       "blue3" "magenta4" "cyan4" "white"])
(add-hook 'shell-mode-hook 'ansi-color-for-comint-mode-on)
(add-hook 'shell-mode-hook 
     '(lambda () (toggle-truncate-lines 1)))
(setq comint-prompt-read-only t)