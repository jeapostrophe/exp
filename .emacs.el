;;;; Based a lot on https://github.com/avar/dotemacs/blob/726f0b6cd5badce641be6euf690ca82e9dbdcc605/.emacs

(add-to-list 'load-path "~/.emacs.d/")

(byte-recompile-directory "~/.emacs.d/")

;;;; Do we have X? This is false under Debian's emacs-nox package
;;;; where many features are compiled out
(defvar emacs-has-x
  (fboundp 'tool-bar-mode))

;;;; Emacs' interface

(setq initial-buffer-choice "~/.emacs.el")

;; Don't get weird properties when pasting
(setq yank-excluded-properties t)

;; Kill menu, tool and scrollbars with fire!
(when emacs-has-x
  (scroll-bar-mode -1))

;; Bell
(setq ring-bell-function 'ignore)
(setq visible-bell t)

;; Don't ever use graphic dialog boxes
(setq use-dialog-box nil)

;; Don't open new annoying windows under X, use the echo area
(when emacs-has-x
  (tooltip-mode -1))

;; Don't display the 'Welcome to GNU Emacs' buffer on startup
(setq inhibit-startup-message t)

;; Display this instead of "For information about GNU Emacs and the
;; GNU system, type C-h C-a.". This has been made intentionally hard
;; to customize in GNU Emacs so I have to resort to hackery.
(defun display-startup-echo-area-message ()
  (message ""))

;; Don't insert instructions in the *scratch* buffer
(setq initial-scratch-message nil)

;; Display the line and column number in the modeline
(setq line-number-mode t)
(setq column-number-mode t)
(line-number-mode t)
(column-number-mode t)

;; syntax highlight everywhere
(global-font-lock-mode t)

;; Show matching parens
(show-paren-mode t)
(setq show-paren-style 'expression)
(setq show-paren-delay 0.0)

;; Show matching paren, even if off-screen
(defadvice show-paren-function
  (after show-matching-paren-offscreen activate)
  "If the matching paren is offscreen, show the matching line in the
        echo area. Has no effect if the character before point is not of
        the syntax class ')'."
  (interactive)
  (if (not (minibuffer-prompt))
      (let ((matching-text nil))
        ;; Only call `blink-matching-open' if the character before point
        ;; is a close parentheses type character. Otherwise, there's not
        ;; really any point, and `blink-matching-open' would just echo
        ;; "Mismatched parentheses", which gets really annoying.
        (if (char-equal (char-syntax (char-before (point))) ?\))
            (setq matching-text (blink-matching-open)))
        (if (not (null matching-text))
            (message matching-text)))))

(set-face-background 'show-paren-match-face "lavender")

;; Highlight selection
(transient-mark-mode t)

;; make all "yes or no" prompts show "y or n" instead
(fset 'yes-or-no-p 'y-or-n-p)

;; Switching
(iswitchb-mode 1)
(icomplete-mode 1)

;; Smash the training wheels
(put 'narrow-to-region 'disabled nil)
(put 'not-modified 'disabled t)
(put 'upcase-region 'disabled nil)
(put 'downcase-region 'disabled nil)
(put 'erase-buffer 'disabled nil)
(put 'dired-find-alternate-file 'disabled nil)

;; I use version control, don't annoy me with backup files everywhere
(setq make-backup-files nil)
(setq auto-save-default nil)

;; Make C-h a act as C-u C-h a
(setq apropos-do-all t)

;; For C-u C-x v d. Probably a good idea for everything else too
(setq completion-ignore-case t)

;; Ask me whether to add a final newline to files which don't have one
(setq require-final-newline t)

;;;; User info
(setq user-full-name "Jay McCarthy")
(setq user-mail-address "jay.mccarthy@gmail.com")

;;; Used in ChangeLog entries
(setq add-log-mailing-address user-mail-address)

;;;; Encoding

;; I use UTF-8 for everything on my systems, some of the below might
;; be redundant.
(setq locale-coding-system 'utf-8)
(set-terminal-coding-system 'utf-8)
(set-keyboard-coding-system 'utf-8)
(set-selection-coding-system 'utf-8)
(setq file-name-coding-system 'utf-8)
(prefer-coding-system 'utf-8)
(set-default-coding-systems 'utf-8)

;;;; Indenting

;; Use spaces, not tabs
(setq indent-tabs-mode nil)
(setq-default indent-tabs-mode nil)

;; Use 4 spaces
(setq default-tab-width 4)
(setq tab-width 4)

(setq backward-delete-char-untabify nil)

;;;; Mode settings

;;;;; compiling
(setq compilation-scroll-output 'yes)
(setq comint-prompt-read-only t)

;; ANSI colors in command interaction and compile:
(require 'ansi-color)
(defun colorize-compilation-buffer ()
  (toggle-read-only)
  (ansi-color-apply-on-region (point-min) (point-max))
  (toggle-read-only))
(add-hook 'compilation-filter-hook 'colorize-compilation-buffer)

;; Found these in one place
(setq ansi-color-names-vector
      ["black" "red4" "green4" "yellow4"
       "blue3" "magenta4" "cyan4" "white"])
;; http://emacsworld.blogspot.com/2009/02/setting-term-mode-colours.html
(setq ansi-term-color-vector
      [unspecified "#000000" "#963F3C" "#5FFB65" "#FFFD65"
                   "#0082FF" "#FF2180" "#57DCDB" "#FFFFFF"])

;;;;; conf-mode
(add-to-list 'auto-mode-alist '("\\.gitconfig$" . conf-mode))

;;;;; flyspell-mode
(setq-default ispell-program-name "/opt/local/bin/ispell")

;;;;; simple.el
(defadvice kill-ring-save (before slickcopy activate compile)
  "When called interactively with no active region, copy
 a single line instead."
  (interactive
   (if mark-active (list (region-beginning) (region-end))
     (list (line-beginning-position)
           (line-beginning-position 2)))))

(defadvice kill-region (before slickcut activate compile)
  "When called interactively with no active region, kill
 a single line instead."
  (interactive
   (if mark-active (list (region-beginning) (region-end))
     (list (line-beginning-position)
           (line-beginning-position 2)))))

;;;;; Comint
(setq comint-buffer-maximum-size (expt 2 16))

;;;;; Dired
(add-hook 'dired-mode-hook
          '(lambda ()
             ;; Only open one dired buffer at most
             (define-key dired-mode-map (kbd "RET") 'dired-find-alternate-file)
             ;; Edit files in dired with "e", which previously did what "RET" did
             (define-key dired-mode-map "e" 'wdired-change-to-wdired-mode)))

;;;;; emacs-lisp-mode

(add-hook 'emacs-lisp-mode-hook 'eldoc-mode t)

;;;;; eshell-mode

;; Don't display the "Welcome to the Emacs shell" banner
(defun eshell-banner-message "")

;;;;; gdb

;; Turn off the new emacs 22 UI
(setq gdb-many-windows nil)

;;;;; Info-mode

;; scroll to subnodes by default
(setq Info-scroll-prefer-subnodes t)

;;;;; progmodes

;; Settings for progmodes (cperl, c-mode etc.)

(dolist (mode '(c-mode
                java-mode
                html-mode-hook
                css-mode-hook
                emacs-lisp-mode))
  (font-lock-add-keywords mode
                          '(("\\(XXX\\|FIXME\\|TODO\\)"
                             1 font-lock-warning-face prepend))))

;;;;; shell-mode

(add-hook
 'shell-mode-hook
 'ansi-color-for-comint-mode-on)

;;;;; Tramp
(setq tramp-default-method "ssh")

;;;;; vc

;; This could be made portable but I'm not interested in that at the
;; moment so it's git-only.

(defun vc-push-or-pull ()
  "`vc-push' if given an argument, otherwise `vc-pull'"
  (interactive)
  (if current-prefix-arg
      (vc-push)
    (vc-pull)))

(defun vc-push ()
  "Run git-push on the current repository, does a dry-run unless
given a prefix arg."
  (interactive)
  (shell-command "git push"))

(defun vc-pull ()
  "Run git-pull on the current repository."
  (interactive)
  (shell-command "git up"))

;;;;; woman

;; Use woman instead of man
(defalias 'man 'woman)

;;;; Packages

;;;;; start server for emacsclient
(setq server-use-tcp t)
(setq server-host "localhost")
(setq server-name "lightning")

(defadvice make-network-process (before force-tcp-server-ipv4 activate)
  "Monkey patch the server to force the port"
  (if (string= "lightning" (plist-get (ad-get-args 0) :name))
      (ad-set-args 0 (plist-put (ad-get-args 0) :service 50000))))

(server-start)

;;;;; line numbering
;(global-linum-mode 1)

;(setq linum-disabled-modes-list '(eshell-mode term-mode compilation-mode org-mode))
;(defun linum-on ()
;  (unless (or (minibufferp) (member major-mode linum-disabled-modes-list))
;    (linum-mode 1)))

;;;;; highlight current line
(global-hl-line-mode 1)
(set-face-background 'hl-line "#f5f5f5")

;;;;; auto-fill
(add-hook 'text-mode-hook 'turn-on-auto-fill)

;;;; multi-term ()
(require 'multi-term)
(setq multi-term-program "/opt/local/bin/zsh")

;;;;; quack
;;(require 'quack)
(add-to-list 'auto-mode-alist '("\\.rkt$" . scheme-mode))
(add-to-list 'auto-mode-alist '("\\.rktl$" . scheme-mode))
(add-to-list 'auto-mode-alist '("\\.rktd$" . scheme-mode))
(add-to-list 'auto-mode-alist '("\\.ss$" . scheme-mode))
(add-to-list 'auto-mode-alist '("\\.scm$" . scheme-mode))

;;;; Platform specific settings

;;;;; Mac OS X

(when (eq window-system 'mac)
  (setq default-input-method "MacOSX")
  (mac-setup-inline-input-method)
  ;;(add-hook 'minibuffer-setup-hook 'mac-change-language-to-us)
  )

(when (eq system-type 'darwin)
  ;; Use the default osx browser to browse urls since w3m isn't
  ;; installed on osx.
  ;; From: http://www.emacswiki.org/cgi-bin/wiki/osx_browse-url-browser-function
  (defun rcy-browse-url-default-macosx-browser (url &optional new-window)
    (interactive (browse-url-interactive-arg "URL: "))
    (let ((url
           (if (aref (url-generic-parse-url url) 0)
               url
             (concat "http://" url))))
      (start-process (concat "open " url) nil "open" url)))

  (setq browse-url-browser-function 'rcy-browse-url-default-macosx-browser))

;;;; global-set-key

;; Replace the standard way of looking through buffers
(progn
  (global-set-key (kbd "C-x C-b") 'ibuffer))

;; Setup some font size changers
(define-key global-map (kbd "C-=") 'text-scale-increase)
(define-key global-map (kbd "C--") 'text-scale-decrease)

;; DrRacket-like compiler
(defun run-current-file (writep)
  "Execute or compile the current file."
  (interactive)
  (let (suffixMap fname suffix progName cmdStr)

    ;; a keyed list of file suffix to comand-line program path/name
    (setq suffixMap
          '(("java" . "javai")
            ("c" . "cci")
            ("cc" . "ccci")
            ("rkt" . "rk")
            ("tex" . "pdflatex")))

    (save-buffer)

    (setq fname (buffer-file-name))
    (setq suffix (file-name-extension fname))
    (setq progName (cdr (assoc suffix suffixMap)))
    (setq cmdStr (concat "-i -c \'" progName " \""   fname "\"\'"))

    (if (string-equal suffix "el") ; special case for emacs lisp
        (load-file fname)
      (if progName
          (progn
            (message "Running...")
            (if (not writep)
                (compile (concat "zsh " cmdStr))
              (let ((multi-term-program-switches 
                     (list "-i" "-c" (concat progName " \"" fname "\""))))
                (multi-term-dedicated-open))))
        (progn
          (message "No recognized program file suffix for this file."))))))
(defun run-current-file-ro () 
  "Execute or compile the current file."
  (interactive)
  (run-current-file nil))
(defun run-current-file-wr () 
  "Execute or compile the current file."
  (interactive)
  (run-current-file t))

(global-set-key (kbd "C-t") 'run-current-file-ro)
(global-set-key (kbd "C-M-t") 'run-current-file-wr)

;; A few editing things
(progn
  (global-set-key (kbd "C-c C-i") 'indent-region)
  (global-set-key (kbd "C-c C-c") 'comment-region)
  (global-set-key (kbd "C-c C-v") 'uncomment-region)
  (global-set-key (kbd "C-c q") 'query-replace)
  (global-set-key (kbd "C-c Q") 'query-replace-regexp)
  (global-set-key (kbd "C-c o") 'occur)
  (global-set-key (kbd "C-c d") 'cd)
  (global-set-key (kbd "C-c f") 'find-dired)
  (global-set-key (kbd "C-c g") 'grep))

(defun my-indent-buffer ()
  "Indent the buffer"
  (interactive)

  (save-excursion
    (delete-trailing-whitespace)
    (indent-region (point-min) (point-max) nil)
    (untabify (point-min) (point-max))))

(global-set-key (kbd "s-i") 'my-indent-buffer)

(progn
  (global-set-key (kbd "C-h F") 'find-function-at-point))

;; vc.el - add commands to push and pull with git
(progn
  (define-key vc-prefix-map "p" 'vc-push-or-pull))

;; turn off the ability to kill
(defun custom-cxcc ()
  "Kill the buffer and the frame"
  (interactive)

  (progn
    (kill-buffer)
    (delete-frame)))

(global-set-key (kbd "C-x C-c") 'custom-cxcc)

(global-set-key (kbd "s-r") 'revert-buffer)
(global-set-key (kbd "M-r") 'replace-string)

(global-set-key (kbd "<s-up>") 'beginning-of-buffer)
(global-set-key (kbd "<s-down>") 'end-of-buffer)
(global-set-key (kbd "<s-left>") 'move-beginning-of-line)
(global-set-key (kbd "<s-right>") 'move-end-of-line)

(global-set-key (kbd "<M-left>") 'backward-sexp)
(global-set-key (kbd "<M-right>") 'forward-sexp)

;; For grading
(defun custom-sl ()
  "Submit grade"
  (interactive)

  (progn
    (save-buffer)
    (server-edit)))

(global-set-key (kbd "s-l") 'custom-sl)

(normal-erase-is-backspace-mode 1)

;; Auto saving
(defun je/save-all ()
  "Save all buffers"
  (interactive)
  (save-some-buffers t))

(run-with-idle-timer 60 t 'je/save-all)
(global-set-key (kbd "s-S") 'je/save-all)

;; Org Mode
(setq load-path (cons "~/Dev/dist/org-mode/lisp" load-path))
(setq load-path (cons "~/Dev/dist/org-mode/contrib/lisp" load-path))
(add-to-list 'Info-default-directory-list
             (expand-file-name "~/Dev/dist/org-mode/doc"))
(require 'org-install)
(require 'org-faces)
(add-to-list 'auto-mode-alist '("\\.org\\'" . org-mode))

(setq org-directory "~/Dev/scm/github.jeapostrophe/home/etc/")
(setq org-default-notes-file "~/Dev/scm/github.jeapostrophe/home/etc/notes.org")
(setq org-agenda-files (list org-directory))

;; XXX change line to gray/italics/crossed out (if the change to white does not persist)
(global-set-key (kbd "s-t")
                (lambda () 
                  (interactive)
                  (if (eq major-mode 'org-mode)
                      (org-todo)
                    (org-agenda-todo))))

(setq org-hide-leading-stars t)
(setq org-return-follows-link t)
(setq org-completion-use-ido t)
(setq org-log-done t)
(setq org-clock-modeline-total 'current)
(setq org-support-shift-select t)
(setq org-agenda-skip-deadline-if-done t)
(setq org-agenda-skip-scheduled-if-done t)
(setq org-agenda-start-on-weekday nil)
(setq org-agenda-include-diary nil)
(setq org-agenda-remove-tags t)
(setq org-agenda-restore-windows-after-quit t)
(setq org-enforce-todo-dependencies t)
(setq org-agenda-dim-blocked-tasks t)
(setq org-agenda-repeating-timestamp-show-all t)
(setq org-agenda-show-all-dates t)
(setq org-timeline-show-empty-dates nil)
(setq org-ctrl-k-protect-subtree t) 
(setq org-use-property-inheritance nil)

(setq org-agenda-todo-ignore-scheduled 'future)
;; Doesn't have an effect in todo mode
;;(setq org-agenda-ndays 365)
(setq org-agenda-cmp-user-defined 'je/agenda-sort)
(setq org-agenda-sorting-strategy '(user-defined-up))
(setq org-agenda-overriding-columns-format "%72ITEM %DEADLINE")
(setq org-agenda-overriding-header "Herr Professor, tear down this TODO list!")

;; XXX Make some more for getting %x, %a, and %i
(setq org-capture-templates
      '(("t" "Todo" entry (file+headline org-default-notes-file "Tasks")
         "* TODO %?\n  SCHEDULED: %T\tDEADLINE: %T\n%a")))
(global-set-key (kbd "s-p") (lambda () (interactive) (org-capture nil "t")))

(setq org-agenda-custom-commands '())

(add-hook 'org-finalize-agenda-hook
    (lambda () 
      (remove-text-properties
       (point-min) (point-max) '(mouse-face t))))

(setq org-agenda-before-sorting-filter-function 'je/todo-color)

;;; These are the default colours from OmniFocus
(defface je/due
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for due items"
  :group 'org-faces)
(set-face-foreground 'je/due "#d0000f")

(defface je/today
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for today items"
  :group 'org-faces)
(set-face-foreground 'je/today "#dd6e0d")

(defface je/soon
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for soon items"
  :group 'org-faces)
(set-face-foreground 'je/soon "#006633")

(defface je/near
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for near items"
  :group 'org-faces)
(set-face-foreground 'je/near "#7f007f")

(defface je/normal
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for normal items"
  :group 'org-faces)
(set-face-foreground 'je/normal "#000000")

(defface je/distant
  (org-compatible-face nil
    '((t (:foreground "#000000"))))
  "Face for distant items"
  :group 'org-faces)
(set-face-foreground 'je/distant "#595959")

(defun je/todo-color (a)
  "Color things in the column view differently based on deadline"
  (let* ((ma (or (get-text-property 1 'org-marker a)
                 (get-text-property 1 'org-hd-marker a)))
         (tn (org-float-time (org-current-time)))
         
         (sa (org-entry-get ma "SCHEDULED"))
         (da (org-entry-get ma "DEADLINE"))

         (ta (if da (org-time-string-to-seconds da) 1.0e+INF))
         (a-day (if da (time-to-days (seconds-to-time ta)) 0))
         (sta (if sa (org-time-string-to-seconds sa) 0)))
    ;; Remove the TODO
    (put-text-property 0 (length a)
                       'txt
                       (replace-regexp-in-string "^TODO *" "" (get-text-property 0 'txt a))
                       a)

    (put-text-property
     0 (length a)
     'face
     (cond
      ((< ta tn)
       ;; The deadline has passed
       'je/due)
      ((= a-day (org-today))
       ;; The deadline is today
       'je/today)
      ((< ta (+ tn (* 60 60 24)))
       ;; The deadline is in the next day
       'je/soon)
      ((< ta (+ tn (* 60 60 24 7)))
       ;; The deadline is in the next week
       'je/near)
      ((< ta (+ tn (* 60 60 24 7 4 )))
       ;; The deadline is in the next four weeks
       'je/normal)
      (t 
       'je/distant))
     a)

    (if (< tn sta)
        nil
      a)))

(defun je/todo-list ()
  "Open up the org-mode todo list"
  (interactive)

  (progn
    (org-agenda "" "t")
    (org-agenda-columns)))

(global-set-key (kbd "s-o") 'je/todo-list)

(defun je/agenda-sort (a b)
  "Sorting strategy for agenda items."
  (let* ((ma (or (get-text-property 1 'org-marker a)
                 (get-text-property 1 'org-hd-marker a)))
         (mb (or (get-text-property 1 'org-marker b)
                 (get-text-property 1 'org-hd-marker b)))
         (def 1.0e+INF)
         (da (org-entry-get ma "DEADLINE"))
         (ta (if da (org-time-string-to-seconds da) def))
         (db (org-entry-get mb "DEADLINE"))
         (tb (if db (org-time-string-to-seconds db) def)))
    (cond ((< ta tb) -1)
          ((< tb ta) +1)
          (t nil))))

;; Eli Calc
(if (locate-library "calculator")
    (progn
      (autoload 'calculator "calculator"
        "Run the Emacs calculator." t)
      (global-set-key [(control return)] 'calculator)))

;; Customized mode line
;(setq load-path (cons "~/Dev/dist/nyan-mode" load-path))
;(require 'nyan-mode)
;(nyan-start-animation)
;(require 'mega-mode)
;(mega-start-animation)

(defun cute-create ()
;  (mega-create))
  (nyan-create))

;; Mode line setup
(setq-default
 mode-line-format
 '(; nyan-mode uses nyan cat as an alternative to %p
   ;(:eval (list (cute-create)))
   (:propertize "%p" face mode-line-folder-face)
   " "
   ; Position, including warning for 80 columns
   (:propertize "%4l:" face mode-line-position-face)
   (:eval (propertize "%3c" 'face
                      (if (>= (current-column) 80)
                          'mode-line-80col-face
                        'mode-line-position-face)))
   ; emacsclient [default -- keep?]
   ;mode-line-client
   ; read-only or modified status
   " "
   (:eval
    (cond (buffer-read-only
           (propertize " RO " 'face 'mode-line-read-only-face))
          ((buffer-modified-p)
           (propertize " ** " 'face 'mode-line-modified-face))
          (t "      ")))
   " "
   ; directory and buffer/file name
   (:propertize (:eval (shorten-directory default-directory 5))
                face mode-line-folder-face)
   (:propertize "%b"
                face mode-line-filename-face)
   ; narrow [default -- keep?]
   ;" %n "
   ; mode indicators: vc, recursive edit, major mode, minor modes, process, global
   ;(vc-mode vc-mode)
   "  %["
   (:propertize mode-name
                face mode-line-mode-face)
   "%] "
   (:eval (propertize (format-mode-line minor-mode-alist)
                      'face 'mode-line-minor-mode-face))
   (:propertize mode-line-process
                face mode-line-process-face)
   (global-mode-string global-mode-string)))

;; Helper function
(defun shorten-directory (dir max-length)
  "Show up to `max-length' characters of a directory name `dir'."
  (let ((path (reverse (split-string (abbreviate-file-name dir) "/")))
        (output ""))
    (when (and path (equal "" (car path)))
      (setq path (cdr path)))
    (while (and path (< (length output) (- max-length 4)))
      (setq output (concat (car path) "/" output))
      (setq path (cdr path)))
    (when path
      (setq output (concat ".../" output)))
    output))

;; Extra mode line faces
(make-face 'mode-line-read-only-face)
(make-face 'mode-line-modified-face)
(make-face 'mode-line-folder-face)
(make-face 'mode-line-filename-face)
(make-face 'mode-line-position-face)
(make-face 'mode-line-mode-face)
(make-face 'mode-line-minor-mode-face)
(make-face 'mode-line-process-face)
(make-face 'mode-line-80col-face)

(defvar light-text "") (setq light-text "black")
(defvar background "") (setq background "gray95")
(defvar light-text-inactive "") (setq light-text-inactive light-text)
(defvar background-inactive "") (setq background-inactive background)
(defvar foreground-warning "") (setq foreground-warning "#c82829")
(defvar background-warning "") (setq background-warning background)
(defvar bright-text "") (setq bright-text foreground-warning)
(defvar foreground-process "") (setq foreground-process "#718c00")

(set-face-attribute 'mode-line nil
    :foreground light-text :background background
    :inverse-video nil
    :box `(:line-width 6 :color ,background :style nil))
(set-face-attribute 'mode-line-inactive nil
    :foreground light-text-inactive :background background-inactive
    :inverse-video nil
    :box `(:line-width 6 :color ,background-inactive :style nil))

(set-face-attribute 'mode-line-read-only-face nil
    :inherit 'mode-line-face
    :foreground foreground-warning
    :background background-warning
    :box `(:line-width 2 :color ,foreground-warning))
(set-face-attribute 'mode-line-modified-face nil
    :inherit 'mode-line-face
    :foreground foreground-warning
    :background background-warning
    :box `(:line-width 2 :color ,foreground-warning))
(set-face-attribute 'mode-line-folder-face nil
    :inherit 'mode-line-face
    :foreground light-text)
(set-face-attribute 'mode-line-filename-face nil
    :inherit 'mode-line-face
    :foreground bright-text
    :weight 'bold)
(set-face-attribute 'mode-line-position-face nil
    :inherit 'mode-line-face
    :family "Menlo" :height 100)
(set-face-attribute 'mode-line-mode-face nil
    :inherit 'mode-line-face
    :foreground light-text-inactive)
(set-face-attribute 'mode-line-minor-mode-face nil
    :inherit 'mode-line-mode-face
    :foreground background-inactive
    :height 110)
(set-face-attribute 'mode-line-process-face nil
    :inherit 'mode-line-face
    :foreground foreground-process)
(set-face-attribute 'mode-line-80col-face nil
    :inherit 'mode-line-position-face
    :foreground foreground-warning :background background-warning)

;; Desktop
;; save a list of open files in ~/.emacs.desktop
;; save the desktop file automatically if it already exists
(setq desktop-path '("~/.emacs.d/"))
(setq desktop-dirname "~/.emacs.d/")
(setq desktop-base-file-name "emacs-desktop")
(setq desktop-save 'if-exists)
(desktop-save-mode 1)

;; save a bunch of variables to the desktop file
;; for lists specify the len of the maximal saved data also
(setq desktop-globals-to-save
      (append '((extended-command-history . 30)
                (file-name-history        . 100)
                (grep-history             . 30)
                (compile-history          . 30)
                (minibuffer-history       . 50)
                (query-replace-history    . 60)
                (read-expression-history  . 60)
                (regexp-history           . 60)
                (regexp-search-ring       . 20)
                (search-ring              . 20)
                (shell-command-history    . 50)
                tags-file-name
                register-alist)))

;;;;; shift select
(setq shift-select-mode 1)
(delete-selection-mode 1)

;; Auto pair
(add-to-list 'load-path "~/Dev/dist/autopair-read-only")
(require 'autopair)

(add-hook 'scheme-mode-hook #'(lambda () (autopair-mode)))
(add-hook 'emacs-lisp-mode-hook #'(lambda () (autopair-mode)))

;; CUA
(setq cua-enable-cua-keys nil)           ;; don't add C-x,C-c,C-v
(cua-mode t)                             ;; for rectangles, CUA is nice

(add-hook 'term-mode-hook
  #'(lambda () (setq autopair-dont-activate t)))

(put 'autopair-insert-opening 'delete-selection t)
(put 'autopair-skip-close-maybe 'delete-selection t)
(put 'autopair-insert-or-skip-quote 'delete-selection t)
(put 'autopair-extra-insert-opening 'delete-selection t)
(put 'autopair-extra-skip-close-maybe 'delete-selection t)
(put 'autopair-backspace 'delete-selection 'supersede)
(put 'autopair-newline 'delete-selection t)

;; Rainbow delimiters
(add-to-list 'load-path "~/Dev/dist/rainbow-delimiters")
(require 'rainbow-delimiters)
(global-rainbow-delimiters-mode t)

;; Twelf
;;(setq twelf-root "/Users/jay/Dev/dist/Twelf/")
;;(load (concat twelf-root "emacs/twelf-init.el"))

;; dynamic abbreviations
(setq dabbrev-case-fold-search nil)
;; XXX make this play nicer with C++
;; maybe try auto-complete-mode

;; Auto saving
;(autoload 'paredit-mode "paredit"
;  "Minor mode for pseudo-structurally editing Lisp code." t)
;(add-hook 'emacs-lisp-mode-hook       (lambda () (paredit-mode +1)))
;(add-hook 'lisp-mode-hook             (lambda () (paredit-mode +1)))
;(add-hook 'lisp-interaction-mode-hook (lambda () (paredit-mode +1)))
;(add-hook 'scheme-mode-hook           (lambda () (paredit-mode +1)))

;; Insert lambda
(global-set-key (kbd "s-\\")
                (lambda () (interactive nil) (insert "λ")))

;; GNUS
(setq gnus-select-method
      '(nnimap "gmail"
               (nnimap-address "imap.gmail.com")
               (nnimap-server-port 993)
               (nnimap-stream ssl)))
(setq message-send-mail-function 'smtpmail-send-it
      smtpmail-starttls-credentials '(("smtp.gmail.com" 587 nil nil))
      smtpmail-auth-credentials '(("smtp.gmail.com" 587 "jay.mccarthy@gmail.com" nil))
      smtpmail-default-smtp-server "smtp.gmail.com"
      smtpmail-smtp-server "smtp.gmail.com"
      smtpmail-smtp-service 587
      smtpmail-local-domain "gmail.com")
;;; Make Gnus NOT ignore [Gmail] mailboxes
(setq gnus-ignored-newsgroups "^to\\.\\|^[0-9. ]+\\( \\|$\\)\\|^[\"]\"[#'()]")
;;; Update mail every 60 minutes? (I don't know if this works)
(gnus-demon-add-handler 'gnus-demon-scan-news 60 t)
;;; XXX setup signing
;;; XXX setup RSS feeds?
;;; XXX setup the summary window to display differently: http://www.emacswiki.org/emacs/GnusFormatting


;; TODO
;; unify C-t and C-M-t
;; look into saving more about my emacs setup, like the size and position of frames
;; On startup, open a new terminal frame
;; https://github.com/elibarzilay/eliemacs
;; http://barzilay.org/misc/interactive.rkt
;; http://www.neilvandyke.org/scribble-emacs/
;; http://www.neilvandyke.org/quack/quack.el
;; http://www.rgrjr.com/emacs/emacs_cheat.html
;; bibtex database
;; Use japanese localization?
;; keybinding to run proc on my finance notes
;; auto line wrap at 80
;; make a custom cheat sheet for me
;; duplicate DrRacket's rainbow block highlighting (C, Java, and Racket)
;; get aspell setup and always on
;; setup tramp/ssh
;; always vertically center cursor?
;; change frame title format to show directory
;; setup emacs irc (in particular, how to get notifications and auto-reconnect)
;; break up frames
;; jump to definition (in file)
;; Etags
;; some simple keybindings/commands for creating and editing journal entries, so I don't have to go to a terminal
;; turn current line highlight and vertical center off in same modes that numbering is off
;; can I get gmail in emacs?
;; can I get a calendar?
;; can I get I get gchat?
;; writing in Japanese (with OS X input method... switch charsets by shortcut doesn't work
;; (maybe some keybindings to look things up in jisho? for my dragon ball translation)
;; Can I write blogger blog posts?
;; Integration with git
;; Get racket all nice (quack?)
;; Look through https://github.com/technomancy/emacs-starter-kit
;; racket support is really busted: #; comments don't work and the indent is all wrong
;; setup emacs-w3m
;; growl integration (or growly thing for linux)
;; http://www.mostlymaths.net/2010/12/emacs-30-day-challenge.html
;; http://www.mostlymaths.net/2010/12/emacs-30-day-challenge-update-1-writing.html
;; http://emacs-fu.blogspot.com/2010/12/conkeror-web-browsing-emacs-way.html
;; https://github.com/mooz/keysnail/wiki/
;; http://babbagefiles.blogspot.com/2011/01/conkeror-browsing-web-emacs-style.html
;; learn about paredit
;; http://www.emacswiki.org/emacs/CategoryCryptography
;; http://doc.norang.ca/org-mode.html
;; setup gnus signing
;; setup encryption of password file


(custom-set-variables
  ;; custom-set-variables was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 )
(custom-set-faces
  ;; custom-set-faces was added by Custom.
  ;; If you edit it by hand, you could mess it up, so be careful.
  ;; Your init file should contain only one such instance.
  ;; If there is more than one, they won't work right.
 '(org-column ((t (:background "white" :foreground "black" :strike-through nil :underline nil :slant normal :weight normal :height 120 :family "Monaco")))))
