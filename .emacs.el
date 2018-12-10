;; Emacs internals
(byte-recompile-directory "~/.emacs.d/")

(require 'package)
(setq package-archives '(("gnu" . "http://elpa.gnu.org/packages/")
                         ("melpa" . "http://melpa.milkbox.net/packages/")))
(package-initialize)

;; Require
(require 'cl)
(require 'helm-config)
(require 'ispell)
(require 'flyspell)
(require 'epa-file)
(require 'uniquify)
(require 'math-symbol-lists)
(require 'ibuffer)
(require 'org)
(require 'org-faces)
(require 'org-protocol)
(require 'midnight)
(require 'ansi-color)
(autoload 'calculator "calculator" "Run the Emacs calculator." t)
(autoload 'markdown-mode "markdown-mode.el" "Major mode for editing Markdown files" t)

;; Connect to environment
(setq exec-path (append '("/usr/local/bin") exec-path))
(cond
 ((eq window-system 'ns)
  (setq shell-command-switch "-lc")))

;; Editing environment
(setq yank-excluded-properties t ; Don't get weird properties when pasting
      make-backup-files nil
      auto-save-default nil
      require-final-newline t
      locale-coding-system 'utf-8
      file-name-coding-system 'utf-8
      indent-tabs-mode nil
      default-tab-width 4
      tab-width 4
      backward-delete-char-untabify nil
      shift-select-mode 1
      cua-enable-cua-keys nil
      dabbrev-case-fold-search nil
      completion-ignore-case t)
(setq-default indent-tabs-mode nil)
(set-terminal-coding-system 'utf-8)
(set-keyboard-coding-system 'utf-8)
(set-selection-coding-system 'utf-8)
(prefer-coding-system 'utf-8)
(set-default-coding-systems 'utf-8)
(normal-erase-is-backspace-mode 1)

;; Standard tools
(setq ag-executable "/usr/local/bin/ag")
(setq ag-highlight-search nil)

;; UI
(setq confirm-kill-emacs 'yes-or-no-p
      initial-buffer-choice "~/.emacs.el"
      ring-bell-function 'ignore
      visible-bell t
      inhibit-startup-message t
      initial-scratch-message nil
      use-dialog-box nil
      line-number-mode t
      column-number-mode t
      vc-follow-symlinks t
      browse-url-browser-function 'browse-url-generic
      browse-url-generic-program "open"
      apropos-do-all t
      Info-scroll-prefer-subnodes t)
(fset 'yes-or-no-p 'y-or-n-p)
(put 'narrow-to-region 'disabled nil)
(put 'not-modified 'disabled t)
(put 'upcase-region 'disabled nil)
(put 'downcase-region 'disabled nil)
(put 'erase-buffer 'disabled nil)
(put 'dired-find-alternate-file 'disabled nil)
(defun display-startup-echo-area-message () (message ""))

;; Style
(setq ns-use-titled-windows nil
      ns-pop-up-frames t)
(set-face-attribute 'default nil
                    :font "Triplicate T4c"
                    :height 120)
(setq frame-title-format '(:eval (if (buffer-file-name) (buffer-file-name) "%b")))

(add-to-list 'default-frame-alist '(height . 27))
(add-to-list 'default-frame-alist '(width . 90))
(add-to-list 'default-frame-alist '(undecorated . t))

(progn
  ;; Color Theme

  ;; Don't change the font for some headings and titles
  (setq solarized-use-variable-pitch nil)
  ;; Don't change size of org-mode headlines (but keep other size-changes)
  (setq solarized-scale-org-headlines nil)

  ;; Avoid all font-size changes
  (setq solarized-height-minus-1 1)
  (setq solarized-height-plus-1 1)
  (setq solarized-height-plus-2 1)
  (setq solarized-height-plus-3 1)
  (setq solarized-height-plus-4 1)

  (load-theme 'solarized-light t))

;; Packages

;;; Helm
(setq
 ;; open helm buffer inside current window, not occupy whole other window
 helm-split-window-in-side-p           t
 ;; move to end or beginning of source when reaching top or bottom of source.
 helm-move-to-line-cycle-in-source     t
 ;; search for library in `require' and `declare-function' sexp.
 helm-ff-search-library-in-sexp        t
 ;; scroll 8 lines other window using M-<next>/M-<prior>
 helm-scroll-amount                    8
 helm-ff-file-name-history-use-recentf t
 helm-echo-input-in-header-line t
 helm-autoresize-max-height 0
 helm-autoresize-min-height 50
 helm-M-x-fuzzy-match t
 helm-buffers-fuzzy-matching t
 helm-recentf-fuzzy-match    t
 helm-buffer-max-length nil)

;;; Show parens
(setq show-paren-style 'expression
      show-paren-delay 0.0)
(set-face-background 'show-paren-match-face "lavender")

;;; ibuffer
(define-ibuffer-column je/name ()
  (cond
   ((buffer-file-name buffer)
    (buffer-file-name buffer))
   (t
    (buffer-name buffer))))
(setq ibuffer-use-header-line nil
      directory-abbrev-alist '()
      ibuffer-formats
      '((mark modified " "
              (mode 12 12 :left :elide)
              " "
              je/name)))

;;; spelling
(setq ispell-process-directory (expand-file-name "~/")
      ispell-program-name "aspell"
      ispell-list-command "list"
      ispell-extra-args '("--sug-mode=ultra")
      flyspell-issue-message-flag nil)

;;; Auto pair
(put 'autopair-insert-opening 'delete-selection t)
(put 'autopair-skip-close-maybe 'delete-selection t)
(put 'autopair-insert-or-skip-quote 'delete-selection t)
(put 'autopair-extra-insert-opening 'delete-selection t)
(put 'autopair-extra-skip-close-maybe 'delete-selection t)
(put 'autopair-backspace 'delete-selection 'supersede)
(put 'autopair-newline 'delete-selection t)

;;; Org mode
(setq org-M-RET-may-split-line '((default . t))
      org-hide-leading-stars t
      org-return-follows-link t
      org-completion-use-ido t
      org-log-done t
      org-clock-modeline-total 'current
      org-support-shift-select t
      org-agenda-skip-deadline-if-done t
      org-agenda-skip-scheduled-if-done t
      org-agenda-start-on-weekday nil
      org-agenda-include-diary nil
      org-agenda-remove-tags t
      org-agenda-restore-windows-after-quit t
      org-enforce-todo-dependencies t
      org-agenda-dim-blocked-tasks t
      org-agenda-repeating-timestamp-show-all t
      org-agenda-show-all-dates t
      org-timeline-show-empty-dates nil
      org-ctrl-k-protect-subtree t
      org-use-property-inheritance nil
      org-agenda-todo-keyword-format ""
      org-prefix-format-compiled nil
      org-agenda-use-tag-inheritance nil
      org-agenda-dim-blocked-tasks nil
      org-agenda-ignore-drawer-properties '(effort appt category)
      org-todo-keywords '((sequence "TODO" "DONE")))
(setq org-agenda-prefix-format
      '((agenda . " %i %-12:c%?-12t% s")
        (timeline . "  % s")
        (todo . "%-12:c")
        (tags . " %i %-12:c")
        (search . " %i %-12:c")))
(setq org-time-clocksum-format
      '(:hours "%d" :require-hours t :minutes ":%02d" :require-minutes t))
;; This ensures that headings are not refile targets if they do not
;; already have children.
(defun je/has-children ()
  (save-excursion
    (let ((this-level (funcall outline-level)))
      (outline-next-heading)
      (let ((child-level (funcall outline-level)))
        (> child-level this-level)))))
(setq org-refile-target-verify-function 'je/has-children)

;;; Custom functions
(defun je/unfill-paragraph () "Unfill" (interactive)
       (let ((fill-column (point-max)))
         (fill-paragraph nil)))
(defun je/unfill-region (start end) "Unfill" (interactive "r")
       (let ((fill-column (point-max)))
         (fill-region start end nil)))
(defun je/indent-buffer () "Indent the buffer" (interactive)       
       (save-excursion
         (delete-trailing-whitespace)
         (indent-region (point-min) (point-max) nil)
         (untabify (point-min) (point-max))))
(defun je/custom-cxcc () "Kill the buffer and the frame" (interactive)
       (kill-buffer)
       (delete-frame))
(defun je/delete-window () "Remove window or frame" (interactive)
       (save-current-buffer
         (if (one-window-p 1) (delete-frame) (delete-window))))
(defun je/org-archive-all () "Archive everything that is done" (interactive)
  (org-map-entries 'org-archive-subtree "/DONE" 'file))
(defun je/clear-state-changes () "Clear state changes" (interactive)
       (let ((regexp "- State \"DONE\""))
         (let ((buffer-file-name nil)) ;; HACK for `clone-buffer'
           (with-current-buffer (clone-buffer nil nil)
             (let ((inhibit-read-only t))
               (keep-lines regexp)
               (kill-region (line-beginning-position)
                            (point-max)))
             (kill-buffer)))
         (unless (and buffer-read-only kill-read-only-ok)
           ;; Delete lines or make the "Buffer is read-only" error.
           (flush-lines regexp))))
(defun je/insert-$ (cmd) "Insert result of shell command"
       (interactive (list (read-shell-command "$ ")))
       (shell-command cmd t))
(defun je/save-all () "Save all buffers" (interactive)
       (desktop-save-in-desktop-dir)
       (save-some-buffers t))
(defun je/ibuffer-previous-line () (interactive)
       (previous-line)
       (if (<= (line-number-at-pos) 3)
           (goto-line (count-lines (point-min) (point-max)))))
(defun je/ibuffer-next-line () (interactive)
       (next-line)
       (if (> (line-number-at-pos) (count-lines (point-min) (point-max)))
           (goto-line 4)))
(defun je/org-finalize-agenda-hook ()
  (goto-char (point-min))
  (mapcar (lambda (n) (insert n " ")) je/org-agenda/filter-ctxt)
  ;; xxx strike through
  (mapcar (lambda (n) (insert "!" n " ")) je/org-agenda/filter-ctxt-not)
  (center-line)
  (remove-text-properties
   (point-min) (point-max) '(mouse-face t)))
(defun je/org-meta-return () "org return" (interactive)
       (newline)
       (org-meta-return))
(defun jecolorize-compilation-buffer ()
  (toggle-read-only)
  (ansi-color-apply-on-region compilation-filter-start (point))
  (toggle-read-only))

;; Advice
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
(defadvice show-paren-function (after show-matching-paren-offscreen activate)
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
        (if (and (point)
                 (char-before (point))
                 (char-syntax (char-before (point)))
                 (char-equal (char-syntax (char-before (point))) ?\)))
            (setq matching-text (blink-matching-open)))
        (if (not (null matching-text))
            (message matching-text)))))
(defadvice ibuffer (around ibuffer-point-to-most-recent) ()
           "Open ibuffer with cursor pointed to most recent buffer name"
           (let ((recent-buffer-name (buffer-name)))
             ad-do-it
             (ibuffer-jump-to-buffer recent-buffer-name)))
(ad-activate 'ibuffer)

;; Hooks
(add-hook 'compilation-filter-hook 'je/colorize-compilation-buffer)
(add-hook 'racket-mode-hook #'(lambda () (autopair-mode t)))
(add-hook 'emacs-lisp-mode-hook #'(lambda () (autopair-mode t)))
(add-hook 'term-mode-hook #'(lambda () (setq autopair-dont-activate t)))
(add-hook 'emacs-lisp-mode-hook 'eldoc-mode t)
(add-hook 'org-finalize-agenda-hook 'je/org-finalize-agenda-hook)
(dolist (hook '(text-mode-hook latex-mode-hook org-mode-hook markdown-mode-hook))
  (add-hook hook (lambda () (flyspell-mode 1))))
(dolist (hook '(c++-mode-hook elisp-mode-hook racket-mode-hook))
  (add-hook hook (lambda () (flyspell-prog-mode 1))))
(dolist (hook '(change-log-mode-hook log-edit-mode-hook))
  (add-hook hook (lambda () (flyspell-mode -1))))

;; Aliases
(defalias 'agp 'ag-project)
(defalias 'mg 'magit-status)
(defalias 'isb 'ispell-buffer)
(defalias 'isw 'ispell-word)
(defalias 'man 'woman)

;; Local Keys
(define-key ibuffer-mode-map (kbd "<up>") 'je/ibuffer-previous-line)
(define-key ibuffer-mode-map (kbd "<down>") 'je/ibuffer-next-line)

(org-defkey org-mode-map [(meta return)]  'je/org-meta-return)
(org-defkey org-mode-map [(meta left)]  nil)
(org-defkey org-mode-map [(meta right)] nil)
(org-defkey org-mode-map [(shift meta left)]  nil)
(org-defkey org-mode-map [(shift meta right)] nil)
(org-defkey org-mode-map [(shift up)]          nil)
(org-defkey org-mode-map [(shift down)]        nil)
(org-defkey org-mode-map [(shift left)]        nil)
(org-defkey org-mode-map [(shift right)]       nil)
(org-defkey org-mode-map [(control shift up)]          nil)
(org-defkey org-mode-map [(control shift down)]        nil)
(org-defkey org-mode-map [(control shift left)]        nil)
(org-defkey org-mode-map [(control shift right)]       nil)
(org-defkey org-mode-map (kbd "M-x") 'helm-M-x)
(org-defkey org-mode-map [(meta tab)]  nil)
(org-defkey org-mode-map (kbd "C-[") 'org-metaleft)
(org-defkey org-mode-map (kbd "C-]") 'org-metaright)
(org-defkey org-mode-map (kbd "C-{") 'org-shiftleft)
(org-defkey org-mode-map (kbd "C-}") 'org-shiftright)

;; Global Keys
(global-set-key (kbd "M-x") 'helm-M-x)
(global-set-key (kbd "<C-SPC>") 'calculator)
(global-set-key (kbd "C-S-t") 'eval-region)
(global-set-key (kbd "C-a") 'mark-whole-buffer)
;;(global-set-key (kbd "C-q") 'kill-emacs)
(global-set-key (kbd "s-c") 'clipboard-kill-ring-save)
(global-set-key (kbd "s-x") 'clipboard-kill-region)
(global-set-key (kbd "s-v") 'clipboard-yank)
(global-set-key (kbd "s-n") 'make-frame)
(global-set-key (kbd "C-s") 'save-buffer)
(global-set-key (kbd "S-s") 'save-buffer)
(global-set-key (kbd "C-f") 'isearch-forward)
(global-set-key (kbd "C-S-g") 'isearch-repeat-forward)
(global-set-key (kbd "C-g") 'top-level)
(global-set-key (kbd "C-S") 'je/save-all)
(global-unset-key (kbd "s-j"))
(global-unset-key (kbd "s-S"))

(global-set-key (kbd "C-'") 'next-buffer)
(global-set-key (kbd "C-;") 'previous-buffer)

(global-set-key (kbd "M-w") 'delete-other-windows)

;; Replace the standard way of looking through buffers
(global-set-key (kbd "C-x C-b") 'helm-mini)
(global-set-key (kbd "C-`") 'helm-mini)
(global-set-key (kbd "C-b") 'helm-mini)
(global-set-key (kbd "M-`") 'iswitchb-buffer)
(global-set-key (kbd "M-<tab>") 'other-window)

(global-set-key (kbd "C-=") 'text-scale-increase)
(global-set-key (kbd "C--") 'text-scale-decrease)

(global-set-key (kbd "C-c C-i") 'indent-region)
(global-set-key (kbd "C-c C-c") 'comment-region)
(global-set-key (kbd "C-c C-v") 'uncomment-region)
(global-set-key (kbd "C-c q") 'query-replace)
(global-set-key (kbd "C-c Q") 'query-replace-regexp)
(global-set-key (kbd "C-c o") 'occur)
(global-set-key (kbd "C-c d") 'cd)
(global-set-key (kbd "C-c f") 'find-dired)
(global-set-key (kbd "C-c g") 'grep)

(global-set-key (kbd "C-h F") 'find-function-at-point)

(global-set-key (kbd "C-r") 'revert-buffer)
(global-set-key (kbd "M-r") 'replace-string)

(global-set-key (kbd "<C-up>") 'beginning-of-buffer)
(global-set-key (kbd "<C-down>") 'end-of-buffer)
(global-set-key (kbd "<C-left>") 'move-beginning-of-line)
(global-set-key (kbd "<C-right>") 'move-end-of-line)

(global-set-key (kbd "M-<left>") 'backward-sexp)
(global-set-key (kbd "M-<right>") 'forward-sexp)

(global-set-key (kbd "C-x C-f") 'helm-find-files)
(global-set-key (kbd "s-i") 'je/indent-buffer)
(global-set-key (kbd "C-x C-c") 'je/custom-cxcc)
(global-set-key (kbd "s-w") 'je/delete-window)
(global-set-key (kbd "C-<return>") 'je/run-current-file)

;; Global Modes
(helm-mode 1)
(tool-bar-mode -1)
(menu-bar-mode -1)
(scroll-bar-mode -1)
(tooltip-mode -1)
(line-number-mode t)
(column-number-mode t)
(global-font-lock-mode t)
(show-paren-mode t)
(transient-mark-mode t)
(iswitchb-mode 1)
(icomplete-mode 1)
(desktop-save-mode 1)
(delete-selection-mode 1)
(epa-file-enable)
(fringe-mode 0)

;; Auto modes
(add-to-list 'auto-mode-alist '("\\.org\\'" . org-mode))
(add-to-list 'auto-mode-alist '("\\.ml[ily]?$" . tuareg-mode))
(add-to-list 'auto-mode-alist '("\\.md" . markdown-mode))
(add-to-list 'auto-mode-alist '("\\.gitconfig$" . conf-mode))
(add-to-list 'auto-mode-alist '("\\.dc$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.rkt$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.rktl$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.scrbl$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.rktd$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.ss$" . racket-mode))
(add-to-list 'auto-mode-alist '("\\.scm$" . racket-mode))

;; Who am i?
(setq user-full-name "Jay McCarthy"
      user-mail-address "jay.mccarthy@gmail.com"
      add-log-mailing-address user-mail-address)

;; Where are my files?
(setq org-directory "~/Dev/scm/github.jeapostrophe/home/etc/"
      org-bookmarks-file "~/Dev/scm/github.jeapostrophe/home/etc/bookmarks.org"
      org-default-notes-file "~/Dev/scm/github.jeapostrophe/home/etc/brain.org"
      org-agenda-files (list org-directory))

;; Server
(setq server-use-tcp t
      server-host "localhost"
      server-name "lightning")
(server-start)

;; XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX

;;;;; compiling
(setq compilation-scroll-output 'first-error)
(setq comint-prompt-read-only t)

;;;;; Comint
(setq comint-buffer-maximum-size (expt 2 16))

;;;;; Dired
(setq ls-lisp-format-time-list '("%Y.%m.$d %H:%M:%S" "%Y.%m.$d %H:%M:%S")
      ls-lisp-use-localized-time-format t
      dired-listing-switches "-alho"
      dired-use-ls-dired nil)
(add-hook 'dired-mode-hook
          '(lambda ()
             ;; Only open one dired buffer at most
             (define-key dired-mode-map (kbd "RET") 'dired-find-alternate-file)
             ;; Edit files in dired with "e", which previously did what "RET" did
             (define-key dired-mode-map "e" 'wdired-change-to-wdired-mode)))

;;;;; progmodes

(dolist (mode '(c-mode
                java-mode
                html-mode-hook
                css-mode-hook
                emacs-lisp-mode))
  (font-lock-add-keywords mode
                          '(("\\(XXX\\|FIXME\\|TODO\\)"
                             1 font-lock-warning-face prepend))))

;; DrRacket-like compiler
(defcustom je/racket-test-p t
  "Whether rkt or rk is run"
  :type 'boolean)
;; XXX Move into normal shell script
(defun je/run-current-file ()
  "Execute or compile the current file."
  (interactive)
  (let (suffixMap fname suffix progName cmdStr)
    ;; a keyed list of file suffix to comand-line program path/name
    (setq suffixMap
          `(("java" . "javai")
            ("ll" . "llvmi")
            ("c" . "cci")
            ("sh" . "zsh")
            ("py" . "python")
            ("cc" . "ccci")
            ("glsl" . "glslangValidator")
            ("rkt" . ,(if je/racket-test-p "rkt" "rk"))
            ("ss" . ,(if je/racket-test-p "rkt" "rk"))
            ("dc" . ,(if je/racket-test-p "rkt" "rk"))
            ("scrbl" . ,(if je/racket-test-p "rkt" "rk"))
            ("txt" . "ctxt")
            ("dot" . "dot -Tpdf -O")
            ("tex" . "pdflatex")))

    (save-buffer)

    (setq fname (buffer-file-name))
    (setq suffix (file-name-extension fname))
    (setq progName (cdr (assoc suffix suffixMap)))
    (setq cmdStr (concat "-i -c \'" progName " \""   fname "\"\'"))

    (if (string-equal suffix "el") ; special case for emacs lisp
        (load-file fname)
      (if (and (not (string-equal suffix "ss"))
               (file-exists-p (concat default-directory "/Makefile")))
          (compile (concat "zsh -i -c 'cd \"" default-directory "\" && make'"))
        (if progName
            (compile (concat "zsh " cmdStr))
          (message "No recognized program file suffix for this file."))))))

;; Auto saving

(defvar je/save-timer (run-with-idle-timer 30 t 'je/save-all))

;; Org Mode

(global-set-key (kbd "C-t")
                (lambda ()
                  (interactive)
                  (if (eq major-mode 'org-mode)
                      (org-todo)
                    (progn
                      (org-agenda-todo)
                      ;; XXX I added this because sometimes it would
                      ;; check the same one twice, but this feels slow
                      ;; and hacky
                      (je/todo-list)))))

(setq org-refile-use-outline-path t)
(setq org-outline-path-complete-in-steps t)
(setq org-refile-targets `((nil . (:maxlevel . 20))))



(setq org-agenda-todo-ignore-scheduled 'future)

(setq org-capture-templates
      '(("t" "Todo" entry (file+headline org-default-notes-file "Tasks")
         "* TODO %?\n  SCHEDULED: %T\tDEADLINE: %T\n%a")))

(global-set-key
 (kbd "<C-f1>")
 (lambda () (interactive) (org-capture nil "t")))
(global-set-key
 (kbd "<C-XF86MonBrightnessDown>")
 (lambda () (interactive) (org-capture nil "t")))
(global-set-key
 (kbd "<f1>")
 (lambda () (interactive) (org-capture nil "t")))

(setq org-agenda-before-sorting-filter-function nil)
(setq org-agenda-before-sorting-filter-function 'je/todo-color)
(setq org-agenda-cmp-user-defined 'je/agenda-sort)
(setq org-agenda-sorting-strategy '(user-defined-up))
(setq org-agenda-overriding-columns-format "%56ITEM %DEADLINE")
(setq org-agenda-overriding-header "")

(setq org-agenda-custom-commands
      '(("t" "Todo list" todo "TODO"
         ())))

;;; These are the default colours from OmniFocus
(defface je/due
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for due items"
  :group 'org-faces)
(set-face-foreground 'je/due "#dc322f")

(defface je/today
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for today items"
  :group 'org-faces)
(set-face-foreground 'je/today "#cb4b16")

(defface je/soon
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for soon items"
  :group 'org-faces)
(set-face-foreground 'je/soon "#859900")

(defface je/near
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for near items"
  :group 'org-faces)
(set-face-foreground 'je/near "#6c71c4")

(defface je/normal
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for normal items"
  :group 'org-faces)
(set-face-foreground 'je/normal "#657b83")

(defface je/distant
  (org-compatible-face 'default
    '((t (:foreground "#000000"))))
  "Face for distant items"
  :group 'org-faces)
(set-face-foreground 'je/distant "#93a1a1")

(defvar je/left-col 0)
(setq je/left-col 60)
(defun je/columate (a d)
  (if (> (length a) je/left-col)
      (setq a (concat (substring a 0 je/left-col) "...")))
  (setq d (replace-regexp-in-string "^<" "" d))
  (setq d (replace-regexp-in-string ">$" "" d))
  (setq d (concat d (make-string (- 26 (length d)) ? )))
  (let ((pad (make-string (- 90 (length a) (length d)) ? )))
    (concat a pad d)))

(defcustom je-schedule-flag? t
  "whether the agenda cares about start time"
  :type 'boolean)
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

    ;; Remove the leading *s
    (setq a (replace-regexp-in-string "^[^ ]*: *" "" a))
    (if da
        (setq a (je/columate a da)))

    ;; Remove the old face
    (remove-text-properties
     0 (length a) '((face nil) (fontified nil)) a)

    ;; Put on the new face
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

    ;; Lame to implement filtering here
    (if (or
         ;; If we want quiet and no due date or distant due date, then
         ;; filter
         (and (or (not da)
                  (> ta (+ tn (* 60 60 24 7 8))))
              (member/eq "Quiet" je/org-agenda/filter-ctxt-not))
         ;; If we care about the schedule, and this is after now, then
         ;; drop it.
         (and je-schedule-flag? (< tn sta))
         ;; Look at tags
         (let* ((tag-str (or (org-entry-get ma "TAGS") ""))
                (tags (org-split-string tag-str ":")))
           ;; If there are tags, implement filtering
           (and tags
                (or
                 ;; If all its tags are not what we care about
                 (and je/org-agenda/filter-ctxt
                      (je/andmap
                       (lambda (f)
                         (not (member/eq f tags)))
                       je/org-agenda/filter-ctxt))

                 ;; OR

                 ;; If any of its tags are what we want to ignore
                 (je/ormap
                  (lambda (f)
                    (member/eq f tags))
                  je/org-agenda/filter-ctxt-not)))))
        nil
      a)))

(defun je/andmap (f l)
  (cond
   (l
    (and (funcall f (car l))
         (je/andmap f (cdr l))))
   (t t)))

(defun je/ormap (f l)
  (cond
   (l
    (or (funcall f (car l))
        (je/ormap f (cdr l))))
   (t nil)))

(defun member/eq (o l)
  (or (equal o l)
      (member o l)))

(defun je/todo-list ()
  "Open up the org-mode todo list"
  (interactive)
  (org-agenda "" "t"))

(setq org-agenda-columns-show-summaries nil)
(setq org-agenda-columns-compute-summary-properties nil)
(defun je/column-display (ctitle value)
  (cond
   ((equal ctitle "ITEM")
    (replace-regexp-in-string "^\** " "" value))
   (t
    value)))
(setq org-columns-modify-value-for-display-function 'je/column-display)

(defvar je/org-agenda/filter-mode 0)
(defvar je/org-agenda/filter-modes 4)
(defvar je/org-agenda/filter-ctxt nil)
(defvar je/org-agenda/filter-ctxt-not nil)

(defun je/todo-list/all ()
  "Open up the org-mode todo list (all)"
  (interactive)
  (progn
    (setq je/org-agenda/filter-mode 0
          je/org-agenda/filter-ctxt nil
          je/org-agenda/filter-ctxt-not nil)
    (je/todo-list)))
(global-set-key (kbd "C-o") 'je/todo-list/all)

(defun je/org-agenda/filter-ctxt-toggle (n)
  (cond
   ((member n je/org-agenda/filter-ctxt)
    (setq je/org-agenda/filter-ctxt
          (je/filter-out je/org-agenda/filter-ctxt n))
    (add-to-list 'je/org-agenda/filter-ctxt-not n))
   ((member n je/org-agenda/filter-ctxt-not)
    (setq je/org-agenda/filter-ctxt-not
          (je/filter-out je/org-agenda/filter-ctxt-not n)))
   (t
    (add-to-list 'je/org-agenda/filter-ctxt n))))

(defun je/org-filter (n)
  "Change filter"
  (interactive "sFilter: ")
  (progn (je/org-agenda/filter-ctxt-toggle n)
         (je/todo-list)))

(defun je/filter-out (l o)
  (cond
   (l
    (cond
     ((equal (car l) o)
      (je/filter-out (cdr l) o))
     (t
      (cons (car l) (je/filter-out (cdr l) o)))))
   (t l)))

(defun je/todo-list/home ()
  "Open up the org-mode todo list (home)"
  (interactive)
  (progn
    (setq je/org-agenda/filter-mode
          (% (+ 1 je/org-agenda/filter-mode)
             je/org-agenda/filter-modes))
    (cond
     ((eq je/org-agenda/filter-mode 0)
      (setq je/org-agenda/filter-ctxt nil
            je/org-agenda/filter-ctxt-not nil))
     ((eq je/org-agenda/filter-mode 1)
      (setq je/org-agenda/filter-ctxt nil
            je/org-agenda/filter-ctxt-not (list "Home" "Quiet")))
     ((eq je/org-agenda/filter-mode 2)
      (setq je/org-agenda/filter-ctxt (list "Home")
            je/org-agenda/filter-ctxt-not nil))
     ((eq je/org-agenda/filter-mode 3)
      (setq je/org-agenda/filter-ctxt nil
            je/org-agenda/filter-ctxt-not (list "Home"))))
    (je/todo-list)))
(global-set-key (kbd "C-S-o") 'je/todo-list/home)
(global-set-key (kbd "C-M-o") 'je/todo-list)

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

;; Customized mode line
(setq-default
 mode-line-format
 '((:propertize "%p" face mode-line-folder-face)
   " "
   (:propertize "%4l:" face mode-line-position-face)
   (:eval (propertize "%3c" 'face
                      (if (>= (current-column) 80)
                          'mode-line-80col-face
                        'mode-line-position-face)))
   " "
   (:eval
    (cond (buffer-read-only
           (propertize " RO " 'face 'mode-line-read-only-face))
          ((buffer-modified-p)
           (propertize " ** " 'face 'mode-line-modified-face))
          (t "      ")))
   " "
   (:propertize (:eval (buffer-name)) face mode-line-filename-face)
   "  %[" (:propertize mode-name face mode-line-mode-face) "%] "
   (:eval (propertize (format-mode-line minor-mode-alist)
                      'face 'mode-line-minor-mode-face))
   (:propertize mode-line-process face mode-line-process-face)
   (global-mode-string global-mode-string)))

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

(defvar light-text "") (setq light-text "#657b83")
(defvar background "") (setq background "#eee8d5")
(defvar light-text-inactive "") (setq light-text-inactive light-text)
(defvar background-inactive "") (setq background-inactive background)
(defvar foreground-warning "") (setq foreground-warning "#dc322f")
(defvar background-warning "") (setq background-warning background)
(defvar bright-text "") (setq bright-text foreground-warning)
(defvar foreground-process "") (setq foreground-process "#dc322f")

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
(setq desktop-load-locked-desktop t)

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

;; Insert lambda
(global-set-key (kbd "C-\\")
                (lambda () (interactive nil) (insert "λ")))

;; clean buffer list
(add-to-list 'clean-buffer-list-kill-never-buffer-names
             "/usr/share/dict/words")
(add-to-list 'clean-buffer-list-kill-never-regexps
             "gpg$" "org$")

;; buffer names
(setq uniquify-min-dir-content 90
      uniquify-buffer-name-style 'forward)

;; racket
(load-file "~/.emacs.d/scheme-indent.el")

;; Set up input method
(quail-define-package "je/math" "UTF-8" "Ω" t)
(quail-define-rules ; whatever extra rules you want to define...
 ("\\from"    #X2190)
 ("\\to"      #X2192)
 ("\\lhd"     #X22B2)
 ("\\rhd"     #X22B3)
 ("\\unlhd"   #X22B4)
 ("\\defs"    "≙")
 ("\\skull"   "☠")
 ("\\larr"   "←")
 ("\\rarr"   "→")
 ("\\unrhd"   #X22B5))
(mapc (lambda (x)
        (if (cddr x)
            (quail-defrule (cadr x) (car (cddr x)))))
      (append math-symbol-list-basic math-symbol-list-extended))

(set-input-method "je/math")

;; search is case insensitive
(setq case-fold-search t)
;; XXX I don't know why this works
(setq isearch-mode-hook
      (function (lambda ()
                  (isearch-toggle-case-fold)
                  (isearch-toggle-case-fold))))

;; customs
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-safe-themes
   (quote
    ("d677ef584c6dfc0697901a44b885cc18e206f05114c8a3b7fde674fce6180879" default)))
 '(doc-view-continuous t)
 '(ibuffer-default-sorting-mode (quote filename/process))
 '(ibuffer-display-summary nil)
 '(racket-mode-pretty-lambda t)
 '(racket-mode-rackjure-indent nil)
 '(racket-program "/Users/jay/Dev/scm/plt/racket/bin/racket")
 '(racket-racket-program "/Users/jay/Dev/scm/plt/racket/bin/racket")
 '(racket-raco-program "/Users/jay/Dev/scm/plt/racket/bin/raco")
 '(racket-use-company-mode nil)
 '(safe-local-variable-values
   (quote
    ((coq-prog-name . "/usr/local/Cellar/coq/8.7.1/bin/coqtop")))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(fringe ((((class color) (background "#fdf6e3")) nil)))
 '(org-column ((t (:background "#fdf6e3" :foreground "#657b83"))))
 '(racket-keyword-argument-face ((t (:foreground "#dc322f"))))
 '(racket-paren-face ((t (:foreground "#93a1a1"))))
 '(racket-selfeval-face ((t (:foreground "#859900")))))

;; proof general
(setq proof-assistants '(coq))
(load-file "/usr/local/Cellar/proof-general/4.4_2/share/emacs/site-lisp/proof-general/site-start.d/pg-init.el")
;; XXX make these local to the proof mode
;; proof-display-three-b
;; proof-shell-exit
;; proof-process-buffer
;; proof-activate-scripting

(defun je/proof-back ()
  (interactive)
  (proof-undo-last-successful-command)
  (je/proof-post))
(defun je/proof-forward ()
  (interactive)
  (proof-assert-next-command-interactive)
  (je/proof-post))
(defun je/proof-here ()
  (interactive)
  (proof-goto-point))
(defun je/proof-post ()
  (interactive)
  (proof-shell-wait)
  (cond
   ((pg-response-has-error-location)
    (proof-next-error))
   (t
    (proof-prf))))

(global-set-key (kbd "<M-s-right>") 'je/proof-here)
(global-set-key (kbd "<M-s-return>") 'je/proof-here)
(global-set-key (kbd "<M-s-up>") 'je/proof-back)
(global-set-key (kbd "<M-s-down>") 'je/proof-forward)

(global-set-key (kbd "M-s-÷") 'je/proof-here)
(global-set-key (kbd "M-s-π") 'je/proof-here)
(global-set-key (kbd "M-s-≤") 'je/proof-back)
(global-set-key (kbd "M-s-≥") 'je/proof-forward)
(global-set-key (kbd "M-s-…") 'proof-prf)

(setq proof-shell-process-connection-type nil
      proof-three-window-mode-policy 'hybrid)

(if nil
    (proof-display-three-b 'hybrid))
