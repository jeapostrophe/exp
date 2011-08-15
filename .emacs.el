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
(setq require-final-newline 'ask)

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
(server-start)

;;;;; shift select
(setq shift-select-mode 1)
(delete-selection-mode 1)

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
(require 'quack)
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
                                        ;(add-hook 'minibuffer-setup-hook 'mac-change-language-to-us)
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
(defun run-current-file ()
  "Execute or compile the current file."
  (interactive)
  (let (suffixMap fname suffix progName cmdStr)

    ;; a keyed list of file suffix to comand-line program path/name
    (setq suffixMap
          '(("java" . "javai")
            ("c" . "cci")
            ("cc" . "ccci")
            ("rkt" . "racket -t")))

    (save-buffer)

    (setq fname (buffer-file-name))
    (setq suffix (file-name-extension fname))
    (setq progName (cdr (assoc suffix suffixMap)))
    (setq cmdStr (concat "zsh -i -c \'" progName " \""   fname "\"\'"))

    (if (string-equal suffix "el") ; special case for emacs lisp
        (load-file fname)
      (if progName
          (progn
            (message "Running...")
            (compile cmdStr))
        (progn
          (message "No recognized program file suffix for this file."))))))

(global-set-key (kbd "C-t") 'run-current-file)

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

(global-set-key (kbd "<s-up>") 'beginning-of-buffer)
(global-set-key (kbd "<s-down>") 'end-of-buffer)
(global-set-key (kbd "<s-left>") 'move-beginning-of-line)
(global-set-key (kbd "<s-right>") 'move-end-of-line)

(global-set-key (kbd "<M-left>") 'backward-sexp)
(global-set-key (kbd "<M-right>") 'forward-sexp)

(normal-erase-is-backspace-mode 1)

;; Org Mode
(setq load-path (cons "~/Dev/dist/org-mode/lisp" load-path))
(setq load-path (cons "~/Dev/dist/org-mode/contrib/lisp" load-path))
(add-to-list 'Info-default-directory-list
             (expand-file-name "~/Dev/dist/org-mode/doc"))
(require 'org-install)
(add-to-list 'auto-mode-alist '("\\.org\\'" . org-mode))

(global-set-key "\C-cl" 'org-store-link)
(global-set-key "\C-cc" 'org-capture)
(global-set-key "\C-ca" 'org-agenda)
(global-set-key "\C-cb" 'org-iswitchb)

;; Eli Calc
(if (locate-library "calculator")
    (progn
      (autoload 'calculator "calculator"
        "Run the Emacs calculator." t)
      (global-set-key [(control return)] 'calculator)))

;; TODO
;; On startup, open a new terminal frame
;; https://github.com/elibarzilay/eliemacs
;; http://barzilay.org/misc/interactive.rkt
;; http://www.neilvandyke.org/scribble-emacs/
;; http://www.neilvandyke.org/quack/quack.el
;; http://www.rgrjr.com/emacs/emacs_cheat.html
;; bibtex database
;; grading?
;; Use japanese localization?
;; keybinding to run proc on my finance notes
;; auto line wrap at 80
;; make a custom cheat sheet for me
;; duplicate DrRacket's rainbow block highlighting (C, Java, and Racket)
;; get aspell setup and always on
;; setup tramp/ssh
;; always vertically center cursor?
;; change frame title format to show directory
;; experiment with org-mode rather than omnifocus
;; mobile org mode: http://mobileorg.ncogni.to/
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
;; Can I do my time tracking database?
;; Integration with git
;; Get racket all nice (quack?)
;; Look through https://github.com/technomancy/emacs-starter-kit
;; racket support is really busted: #; comments don't work and the indent is all wrong
