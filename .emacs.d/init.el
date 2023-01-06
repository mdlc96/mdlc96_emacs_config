;; Install straight.el
(defvar bootstrap-version)
(let ((bootstrap-file
       (expand-file-name "straight/repos/straight.el/bootstrap.el" user-emacs-directory))
      (bootstrap-version 5))
  (unless (file-exists-p bootstrap-file)
    (with-current-buffer
        (url-retrieve-synchronously
         "https://raw.githubusercontent.com/raxod502/straight.el/develop/install.el"
         'silent 'inhibit-cookies)
      (goto-char (point-max))
      (eval-print-last-sexp)))
  (load bootstrap-file nil 'nomessage))


(straight-use-package 'use-package)

;; Configure use-package to use straight.el by default
(use-package straight
             :custom (straight-use-package-by-default t))

(use-package auto-package-update
   :ensure t
   :config
   (setq auto-package-update-delete-old-versions t
         auto-package-update-interval 4)
   (auto-package-update-maybe))

; load as soon as possible.
; avoids emacs generating littering files all over the place.
(use-package no-littering
  :ensure t
  :custom
  (setq auto-save-file-name-transforms
	`((".*" ,(no-littering-expand-var-file-name "auto-save/") t))))

;modus themes need to be loaded as soon as possible.
;then load one of them with use-package emacs, if this theme is desired
(use-package modus-themes
  :init
  (setq modus-themes-common-palette-overrides '((comment yellow-cooler)
					;(string green-cooler)
						(bg-paren-match bg-magenta-intense)
						(bg-region bg-ochre) ; try to replace `bg-ochre' with `bg-lavender', `bg-sage'
						(fg-region unspecified))
	modus-themes-italic-constructs t)
  :config
  ;; Load the theme of your choice:
  ;(load-theme 'modus-vivendi :noconfirm)
  :bind ("<f5>" . modus-themes-toggle))

; emacs base config
(use-package emacs
  :init
  (setq inhibit-startup-screen t
	column-number-mode t ; show column number
        line-number-mode t ; show line number
        indent-tabs-mode nil ; always use spaces, not tabs
        enable-recursive-minibuffers t

	compilation-scroll-output t
	compilation-always-kill t
	;make-backup-files nil "Do not make backup files on save buffer."
	;auto-save-default nil "Do not auto-save of every file-visiting buffer."
	create-lockfiles  nil ;Do not use lock-files.
	require-final-newline t) ;Ends file with a newline.
					; find undo management if needed
					;and package to manage selection of words...

  (show-paren-mode t)
  (global-display-line-numbers-mode)

  ;set frame font
  ;; (cond
  ;;  ((find-font (font-spec :name "JetBrains Mono NL"))
  ;;   (set-frame-font "JetBrains Mono NL 14" nil t)))
  (cond
   ((find-font (font-spec :name "IBM Plex Mono"))
    (set-frame-font "IBM Plex Mono 14" nil t)))

  :bind
  ("C-c C-q" . comment-or-uncomment-region))

; manage recent opened files
(use-package recentf
  :after no-littering
  :custom
  (add-to-list 'recentf-exclude no-littering-var-directory)
  (add-to-list 'recentf-exclude no-littering-etc-directory)
  (recentf-mode)
  )

;; easy window navigation
(use-package ace-window
  :ensure t
  :bind ("M-o" . ace-window)
  )

; different color per parenthesis level 
(use-package rainbow-delimiters
  :ensure t
  :hook (prog-mode . rainbow-delimiters-mode)
  )

; smart parenthesis
(use-package smartparens
  :ensure t
  :init
  (require 'smartparens-config)
  :hook (prog-mode . smartparens-mode)
  )

; navigate and highlight keywords in the code
(use-package symbol-overlay
  :ensure t
  :bind (("M-i"  . symbol-overlay-put)
         ("M-n"  . symbol-overlay-switch-forward)
         ("M-p"  . symbol-overlay-switch-backward)
         ("<f7>" . symbol-overlay-mode)
         ("<f8>" . symbol-overlay-remove-all)
         )
  :hook (prog-mode . symbol-overlay-mode)
  )

; smart white space trimmer 
(use-package ws-butler
  :ensure t
  :hook (prog-mode . ws-butler-mode)
  )

; template system for coding.
(use-package yasnippet
  :ensure t
  :init
  ; snippet folder
  (setq yas-snippet-dirs
      '("~/.emacs.d/snippets"))
  (yas-global-mode 1))

; highlight indentation.
(use-package highlight-indent-guides
  :config
  (setq highlight-indent-guides-method 'character
	highlight-indent-guides-responsive 'stack
	highlight-indent-guides-auto-character-face-perc 30
	highlight-indent-guides-delay 0.25)

  :hook
  (prog-mode . highlight-indent-guides-mode))

;; vertico
;; Enable vertico
(use-package vertico
  :straight (vertico :files (:defaults "extensions/*")
                     :includes (vertico-mouse vertico-directory))
  :init
  (vertico-mode)
  
  ;; Different scroll margin
  ;; (setq vertico-scroll-margin 0)
  ;; Show more candidates
  ;; (setq vertico-count 20)

  ;; Grow and shrink the Vertico minibuffer
  ;; (setq vertico-resize t)

  ;; Optionally enable cycling for `vertico-next' and `vertico-previous'.
  ;; (setq vertico-cycle t)

  (vertico-mouse-mode)

  :bind (:map vertico-map
	      ("<tab>" . vertico-directory-enter)
              ;("\t" . vertico-directory-enter) ; \t or \r
              ("\d" . vertico-directory-delete-char)
              ("\M-\d" . vertico-directory-delete-word))
  :hook (rfn-eshadow-update-overlay . vertico-directory-tidy))

; orderless
(use-package orderless
  :init
  ;; Configure a custom style dispatcher (see the Consult wiki)
  ;; (setq orderless-style-dispatchers '(+orderless-dispatch)
  ;;       orderless-component-separator #'orderless-escapable-split-on-space)
  (setq completion-styles '(orderless)
        completion-category-defaults nil
        completion-category-overrides '((file (styles partial-completion)))))

;; Enable rich annotations using the Marginalia package
(use-package marginalia
  ;; Either bind `marginalia-cycle' globally or only in the minibuffer
  :bind (("M-A" . marginalia-cycle)
         :map minibuffer-local-map
         ("M-A" . marginalia-cycle))

  ;; The :init configuration is always executed (Not lazy!)
  :init

  ;; Must be in the :init section of use-package such that the mode gets
  ;; enabled right away. Note that this forces loading the package.
  (marginalia-mode))


;; Example configuration for Consult
(use-package consult
  ;; Replace bindings. Lazily loaded due by `use-package'.
  :bind (;; C-c bindings (mode-specific-map)
         ("C-c h" . consult-history)
         ("C-c m" . consult-mode-command)
         ("C-c k" . consult-kmacro)
         ;; C-x bindings (ctl-x-map)
         ("C-x M-:" . consult-complex-command)     ;; orig. repeat-complex-command
         ("C-x b" . consult-buffer)                ;; orig. switch-to-buffer
         ("C-x 4 b" . consult-buffer-other-window) ;; orig. switch-to-buffer-other-window
         ("C-x 5 b" . consult-buffer-other-frame)  ;; orig. switch-to-buffer-other-frame
         ("C-x r b" . consult-bookmark)            ;; orig. bookmark-jump
         ("C-x p b" . consult-project-buffer)      ;; orig. project-switch-to-buffer
         ;; Custom M-# bindings for fast register access
         ("M-#" . consult-register-load)
         ("M-'" . consult-register-store)          ;; orig. abbrev-prefix-mark (unrelated)
         ("C-M-#" . consult-register)
         ;; Other custom bindings
         ("M-y" . consult-yank-pop)                ;; orig. yank-pop
         ("<help> a" . consult-apropos)            ;; orig. apropos-command
         ;; M-g bindings (goto-map)
         ("M-g e" . consult-compile-error)
         ("M-g f" . consult-flymake)               ;; Alternative: consult-flycheck
         ("M-g g" . consult-goto-line)             ;; orig. goto-line
         ("M-g M-g" . consult-goto-line)           ;; orig. goto-line
         ("M-g o" . consult-outline)               ;; Alternative: consult-org-heading
         ("M-g m" . consult-mark)
         ("M-g k" . consult-global-mark)
         ("M-g i" . consult-imenu)
         ("M-g I" . consult-imenu-multi)
         ;; M-s bindings (search-map)
         ("M-s d" . consult-find)
         ("M-s D" . consult-locate)
         ("M-s g" . consult-grep)
         ("M-s G" . consult-git-grep)
         ("M-s r" . consult-ripgrep)
         ("M-s l" . consult-line)
         ("M-s L" . consult-line-multi)
         ("M-s m" . consult-multi-occur)
         ("M-s k" . consult-keep-lines)
         ("M-s u" . consult-focus-lines)
         ;; Isearch integration
         ("M-s e" . consult-isearch-history)
         :map isearch-mode-map
         ("M-e" . consult-isearch-history)         ;; orig. isearch-edit-string
         ("M-s e" . consult-isearch-history)       ;; orig. isearch-edit-string
         ("M-s l" . consult-line)                  ;; needed by consult-line to detect isearch
         ("M-s L" . consult-line-multi)            ;; needed by consult-line to detect isearch
         ;; Minibuffer history
         :map minibuffer-local-map
         ("M-s" . consult-history)                 ;; orig. next-matching-history-element
         ("M-r" . consult-history))                ;; orig. previous-matching-history-element

  ;; Enable automatic preview at point in the *Completions* buffer. This is
  ;; relevant when you use the default completion UI.
  :hook (completion-list-mode . consult-preview-at-point-mode)

  ;; The :init configuration is always executed (Not lazy)
  :init

  ;; Optionally configure the register formatting. This improves the register
  ;; preview for `consult-register', `consult-register-load',
  ;; `consult-register-store' and the Emacs built-ins.
  (setq register-preview-delay 0.5
        register-preview-function #'consult-register-format)

  ;; Optionally tweak the register preview window.
  ;; This adds thin lines, sorting and hides the mode line of the window.
  (advice-add #'register-preview :override #'consult-register-window)

  ;; Use Consult to select xref locations with preview
  (setq xref-show-xrefs-function #'consult-xref
        xref-show-definitions-function #'consult-xref)

  ;; Configure other variables and modes in the :config section,
  ;; after lazily loading the package.
  :config

  ;; Optionally configure preview. The default value
  ;; is 'any, such that any key triggers the preview.
  ;; (setq consult-preview-key 'any)
  ;; (setq consult-preview-key (kbd "M-."))
  ;; (setq consult-preview-key (list (kbd "<S-down>") (kbd "<S-up>")))
  ;; For some commands and buffer sources it is useful to configure the
  ;; :preview-key on a per-command basis using the `consult-customize' macro.
  (consult-customize
   consult-theme :preview-key '(:debounce 0.2 any)
   consult-ripgrep consult-git-grep consult-grep
   consult-bookmark consult-recent-file consult-xref
   consult--source-bookmark consult--source-file-register
   consult--source-recent-file consult--source-project-recent-file
   ;; :preview-key (kbd "M-.")
   :preview-key '(:debounce 0.4 any))

  ;; Optionally configure the narrowing key.
  ;; Both < and C-+ work reasonably well.
  (setq consult-narrow-key "<") ;; (kbd "C-+")

  ;; Optionally make narrowing help available in the minibuffer.
  ;; You may want to use `embark-prefix-help-command' or which-key instead.
  ;; (define-key consult-narrow-map (vconcat consult-narrow-key "?") #'consult-narrow-help)

  ;; By default `consult-project-function' uses `project-root' from project.el.
  ;; Optionally configure a different project root function.
  ;; There are multiple reasonable alternatives to chose from.
  ;;;; 1. project.el (the default)
  ;; (setq consult-project-function #'consult--default-project--function)
  ;;;; 2. projectile.el (projectile-project-root)
  ;; (autoload 'projectile-project-root "projectile")
  ;; (setq consult-project-function (lambda (_) (projectile-project-root)))
  ;;;; 3. vc.el (vc-root-dir)
  ;; (setq consult-project-function (lambda (_) (vc-root-dir)))
  ;;;; 4. locate-dominating-file
  ;; (setq consult-project-function (lambda (_) (locate-dominating-file "." ".git")))
  (autoload 'projectile-project-root "projectile")
  (setq consult-project-function (lambda (_) (projectile-project-root)))
  )

; embark
(use-package embark
  :ensure t

  :bind
  (("C-." . embark-act)         ;; pick some comfortable binding
   ("C-;" . embark-dwim)        ;; good alternative: M-.
   ("C-h B" . embark-bindings)) ;; alternative for `describe-bindings'

  :init

  ;; Optionally replace the key help with a completing-read interface
  (setq prefix-help-command #'embark-prefix-help-command)

  :config

  ;; Hide the mode line of the Embark live/completions buffers
  (add-to-list 'display-buffer-alist
               '("\\`\\*Embark Collect \\(Live\\|Completions\\)\\*"
                 nil
                 (window-parameters (mode-line-format . none)))))

;; Consult users will also want the embark-consult package.
(use-package embark-consult
  :ensure t ; only need to install it, embark loads it after consult if found
  :hook
  (embark-collect-mode . consult-preview-at-point-mode))

 					; corfu autocompletion
(use-package corfu
  :straight (corfu :files (:defaults "extensions/*")
                   :includes (corfu-info corfu-history))
  :custom
  (corfu-cycle nil)                ;; Enable cycling for `corfu-next/previous'
  (corfu-auto nil)                 ;; Enable auto completion
  (corfu-separator ?\s)          ;; Orderless field separator
  (corfu-quit-at-boundary nil)   ;; Never quit at completion boundary
  (corfu-quit-no-match 'separator)      ;; Never quit, even if there is no match
  (corfu-preview-current nil)    ;; Disable current candidate preview
  (corfu-preselect-first nil)    ;; Disable candidate preselection
  (corfu-on-exact-match nil)     ;; Configure handling of exact matches
  (corfu-echo-documentation nil) ;; Disable documentation in the echo area
  (corfu-scroll-margin 5)        ;; Use scroll margin

  (corfu-min-width 80)
  (corfu-max-width corfu-min-width)     ; Always have the same width
  (corfu-count 10)
  (corfu-auto-delay 0.25)
  (corfu-auto-prefix 3)

  (tab-always-indent 'complete)
  (completion-cycle-threshold nil)

  (setq corfu-popupinfo-delay 0)

  :bind
  ;; Another key binding can be used, such as S-SPC.
  (:map corfu-map
        ("C-SPC" . corfu-insert-separator)
        ([return] . corfu-complete) ;corfu-insert?
         ("C-n" . corfu-next)
            ("C-p" . corfu-previous)
            ("<escape>" . corfu-quit)
            ("<return>" . corfu-insert)
            ("M-d" . corfu-show-documentation)
            ("M-l" . corfu-show-location)
            ("C-SPC" . corfu-insert-separator))
  
  :init
  (global-corfu-mode)
  (corfu-popupinfo-mode)

  :config

  (defun corfu-enable-always-in-minibuffer ()
    "Enable Corfu in the minibuffer if Vertico/Mct are not active."
    (unless (or (bound-and-true-p mct--active) ; Useful if I ever use MCT
                (bound-and-true-p vertico--input))
      (setq-local corfu-auto nil)       ; Ensure auto completion is disabled
      (corfu-mode 1)))
  (add-hook 'minibuffer-setup-hook #'corfu-enable-always-in-minibuffer 1))


(use-package kind-icon
  :after corfu
  ;:disabled
  :custom
  (kind-icon-use-icons nil)
  (kind-icon-default-face 'corfu-default) ; Have background color be the same as `corfu' face background
  (kind-icon-blend-background t)  ; Use midpoint color between foreground and background colors ("blended")?
  (kind-icon-blend-frac 0.08)

  ;; NOTE 2022-02-05: `kind-icon' depends `svg-lib' which creates a cache
  ;; directory that defaults to the `user-emacs-directory'. Here, I change that
  ;; directory to a location appropriate to `no-littering' conventions, a
  ;; package which moves directories of other packages to sane locations.
  (svg-lib-icons-dir (no-littering-expand-var-file-name "svg-lib/cache/")) ; Change cache dir
  :config
  (add-to-list 'corfu-margin-formatters #'kind-icon-margin-formatter) ; Enable `kind-icon'


  ;; Add hook to reset cache so the icon colors match my theme
  ;; NOTE 2022-02-05: This is a hook which resets the cache whenever I switch
  ;; the theme using my custom defined command for switching themes. If I don't
  ;; do this, then the backgound color will remain the same, meaning it will not
  ;; match the background color corresponding to the current theme. Important
  ;; since I have a light theme and dark theme I switch between. This has no
  ;; function unless you use something similar
  (add-hook 'kb/themes-hooks #'(lambda () (interactive) (kind-icon-reset-cache))))

(use-package cape
  :straight (cape :files (:defaults "*")
                  :includes (cape-keyword cape-char))

  ;; Bind dedicated completion commands
  ;; Alternative prefix keys: C-c p, M-p, M-+, ...
  :bind (("C-c p p" . completion-at-point) ;; capf
         ("C-c p t" . complete-tag)        ;; etags
         ("C-c p d" . cape-dabbrev)        ;; or dabbrev-completion
         ("C-c p h" . cape-history)
         ("C-c p f" . cape-file)
         ("C-c p k" . cape-keyword)
         ("C-c p s" . cape-symbol)
         ("C-c p a" . cape-abbrev)
         ("C-c p i" . cape-ispell)
         ("C-c p l" . cape-line)
         ("C-c p w" . cape-dict)
         ("C-c p \\" . cape-tex)
         ("C-c p _" . cape-tex)
         ("C-c p ^" . cape-tex)
         ("C-c p &" . cape-sgml)
         ("C-c p r" . cape-rfc1345))
  :init
  ;; Add `completion-at-point-functions', used by `completion-at-point'.
  (add-to-list 'completion-at-point-functions #'cape-dabbrev)
  (add-to-list 'completion-at-point-functions #'cape-file)
  ;;(add-to-list 'completion-at-point-functions #'cape-history)
  (add-to-list 'completion-at-point-functions #'cape-keyword)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-tex)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-sgml)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-rfc1345)
  (add-to-list 'completion-at-point-functions #'cape-abbrev)
  (add-to-list 'completion-at-point-functions #'cape-ispell)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-dict)
  (add-to-list 'completion-at-point-functions #'cape-symbol)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-line)

  (setq cape-dabbrev-check-other-buffers 'some)

  ; add as hook because of verilog-mode replacing locally completion functions.
  :hook
  (verilog-mode . (lambda()
					;(delete t completion-at-point-functions)
		    (add-to-list 'completion-at-point-functions #'cape-keyword)

		    (add-to-list 'completion-at-point-functions #'cape-file)
		    (add-to-list 'completion-at-point-functions #'cape-dabbrev))))

;;;;;;;;;;;;;;;;

(use-package projectile
  :ensure t
  :init
  (projectile-mode +1)
  :bind (:map projectile-mode-map
              ("s-p" . projectile-command-map)
              ("C-c p" . projectile-command-map)))

(use-package citre
  :defer t
  :init
  ;; This is needed in `:init' block for lazy load to work.
  (require 'citre-config)
  ;; Bind your frequently used commands.  Alternatively, you can define them
  ;; in `citre-mode-map' so you can only use them when `citre-mode' is enabled.
  :config
  (setq
   ;; Set these if readtags/ctags is not in your PATH.
   citre-readtags-program "/path/to/readtags"
   citre-ctags-program "/path/to/ctags"
   ;; Set these if gtags/global is not in your PATH (and you want to use the
   ;; global backend)
   citre-gtags-program "/path/to/gtags"
   citre-global-program "/path/to/global"
   ;; Set this if you use project management plugin like projectile.  It's
   ;; used for things like displaying paths relatively, see its docstring.
   citre-project-root-function #'projectile-project-root
   ;; Set this if you want to always use one location to create a tags file.
   citre-default-create-tags-file-location 'global-cache
   ;; See the "Create tags file" section above to know these options
   citre-use-project-root-when-creating-tags t
   citre-prompt-language-for-ctags-command t
   ;; By default, when you open any file, and a tags file can be found for it,
   ;; `citre-mode' is automatically enabled.  If you only want this to work for
   ;; certain modes (like `prog-mode'), set it like this.
   citre-auto-enable-citre-mode-modes '(prog-mode))

  :bind (:map citre-mode-map
  ("M-." . citre-jump)
  ("C-M-." . citre-jump-back)
  ("M-/" . citre-ace-peek)
  ("C-x c u" . citre-update-this-tags-file)))


					; bookmarks
(use-package bm
  :ensure t
  :demand t

  :init
  ;; restore on load (even before you require bm)
  (setq bm-restore-repository-on-load t)


  :config
  ;; Allow cross-buffer 'next'
  (setq bm-cycle-all-buffers t)

  ;; where to store persistant files
  (setq bm-repository-file "~/.emacs.d/bm-repository")

  ;; save bookmarks
  (setq-default bm-buffer-persistence t)

  ;; Loading the repository from file when on start up.
  (add-hook 'after-init-hook 'bm-repository-load)

  ;; Saving bookmarks
  (add-hook 'kill-buffer-hook #'bm-buffer-save)

  ;; Saving the repository to file when on exit.
  ;; kill-buffer-hook is not called when Emacs is killed, so we
  ;; must save all bookmarks first.
  (add-hook 'kill-emacs-hook #'(lambda nil
                                 (bm-buffer-save-all)
                                 (bm-repository-save)))

  ;; The `after-save-hook' is not necessary to use to achieve persistence,
  ;; but it makes the bookmark data in repository more in sync with the file
  ;; state.
  (add-hook 'after-save-hook #'bm-buffer-save)

  ;; Restoring bookmarks
  (add-hook 'find-file-hooks   #'bm-buffer-restore)
  (add-hook 'after-revert-hook #'bm-buffer-restore)

  ;; The `after-revert-hook' is not necessary to use to achieve persistence,
  ;; but it makes the bookmark data in repository more in sync with the file
  ;; state. This hook might cause trouble when using packages
  ;; that automatically reverts the buffer (like vc after a check-in).
  ;; This can easily be avoided if the package provides a hook that is
  ;; called before the buffer is reverted (like `vc-before-checkin-hook').
  ;; Then new bookmarks can be saved before the buffer is reverted.
  ;; Make sure bookmarks is saved before check-in (and revert-buffer)
  (add-hook 'vc-before-checkin-hook #'bm-buffer-save)


  :bind (("<f2>" . bm-next)
         ("S-<f2>" . bm-previous)
         ("C-<f2>" . bm-toggle))
  )



(use-package verilog-mode
  :init
  (setq verilog-indent-spaces 4
        verilog-indent-level             verilog-indent-spaces
        verilog-indent-level-module      verilog-indent-spaces
        verilog-indent-level-declaration verilog-indent-spaces
        verilog-indent-level-behavioral  verilog-indent-spaces
        verilog-indent-level-directive   1
        verilog-case-indent              verilog-indent-spaces
        verilog-auto-newline             'nil
        verilog-auto-indent-on-newline   t
        verilog-tab-always-indent        t
        verilog-auto-endcomments         t
        verilog-minimum-comment-distance 10
        verilog-indent-begin-after-if    'nil
        verilog-indent-lists             'nil
        verilog-auto-lineup              'declarations)
  
  (defun verilog-extend-font-lock ()
    (font-lock-add-keywords nil '(    
         ; Valid hex number (will highlight invalid suffix though)
         ("'[b o h d][[:xdigit:]]+\\b" . font-lock-warning-face)

         ; number
         ("\\b[0-9]+\\b" . font-lock-string-face)

         ("[+=<>%\\*/:&^\\|-]" . font-lock-type-face)
         ("[!~]" . font-lock-warning-face)
					;("\\[\s*[$]\s*\\]" 1 font-lock-type-face)
	 ("\\[\s*\\([$]\\|[[:alnum:]]+\\)\s*\\]" 1 font-lock-builtin-face)
	 ;("foreach\s*(\s*[[:alnum:]]+\s*[\\([[:alnum:]]+,\\)*\\(\s*\\([[:alnum:]]+\\)\s*,*\\)\s*\\]\s*)" 2 font-lock-builtin-face)
         )))
  :hook (verilog-mode . verilog-extend-font-lock)
  )

(use-package emacs ; without this operandi theme is loaded.
  :init
  :config
  ;; Load the theme of your choice.
  (load-theme 'modus-vivendi :noconfirm))

;;; doom modeline
(use-package doom-modeline
  :ensure t
  :hook (after-init . doom-modeline-mode))

;; (use-package all-the-icons
;;   :ensure t)

(use-package p4
  :ensure t)

;;;;;

(defun init-file-open ()
  (interactive)
  (find-file "~/.emacs.d/init.el"))



;; ;backup files
;; ;all backup files in the same folder.
;; (setq backup-directory-alist `(("." . "~/.saves")))
;; (setq backup-by-copying t)
;; (setq delete-old-versions t
;;   kept-new-versions 6
;;   kept-old-versions 2
;;   version-control t)


;; ;blink parenthesis removed by show paren mode
;; (show-paren-mode t)
;; (require 'flycheck)
;; (add-hook 'prog-mode-hook 'flycheck-mode)
;; (setq flycheck-emacs-lisp-load-path 'inherit)

;; (require 'flycheck-hdl-irun)
;; (setq flycheck-hdl-irun-hdlvar
;;    (concat (getenv "PRJ_HOME") "/env/df2/hdl.var"))
;; (setq flycheck-hdl-irun-args (quote ("-v200x" "-extv200x")))


;; ;; (defun mdc-prog-mode-hook ()
;; ;;     (interactive)
;; ;;     (flymake-mode t))

;; ;; (add-hook 'prog-mode-hook 'mdc-prog-mode-hook)


;; (require 'stupid-indent-mode)
;; (setq stupid-indent-level indent-level)
;; (add-hook 'prog-mode-hook 'stupid-indent-mode)


;; ;; (require 'highlight-indent-guides)
;; ;; (add-hook 'prog-mode-hook 'highlight-indent-guides-mode)
;; ;; (setq highlight-indent-guides-method 'bitmap)
;; ;(setq highlight-indent-guides-character ?|)

;; (require 'highlight-indentation)
;; (add-hook 'prog-mode-hook 'highlight-indentation-mode)

;; (add-to-list 'load-path "~/.emacs.d/lisp/god-mode-master/")
;; (setq god-mode-enable-function-key-translation nil)
;; (require 'god-mode)
;; (global-set-key (kbd "<escape>") #'god-mode-all)

;; (setq god-exempt-major-modes nil)
;; (setq god-exempt-predicates nil)

;; (defun my-god-mode-update-cursor-type ()
;;   (setq cursor-type (if (or god-local-mode buffer-read-only) 'box 'bar)))

;; (add-hook 'post-command-hook #'my-god-mode-update-cursor-type)
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(custom-safe-themes
   '("5a9c693de1999fae9ba09269a4aae08740d6dd342c510e416f42b49f59d63fe0" "3ab376acffab6b4e79ae2b6e0a1cce3fa21dbac0027f0ff0dfef02b5c838dba9" default))
 '(package-selected-packages
   '(verilog-mode p4 yasnippet ws-butler vertico use-package symbol-overlay smartparens rainbow-delimiters projectile orderless no-littering modus-themes marginalia embark-consult doom-modeline corfu citre cape bm all-the-icons ace-window)))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )


(use-package emacs
  :after cape-keyword
  :init
  (add-to-list 'cape-keyword-list
				 '(verilog-mode
				   "and" "buf" "bufif0" "bufif1" "cmos" "defparam" "event" "genvar" "highz0" "highz1" "inout" "input"
				   "integer" "localparam" "mailbox" "nand" "nmos" "nor" "not" "notif0" "notif1" "or"
				   "output" "parameter" "pmos" "pull0" "pull1" "pulldown" "pullup" "rcmos" "real" "realtime"
				   "reg" "rnmos" "rpmos" "rtran" "rtranif0" "rtranif1" "semaphore" "signed" "specparam" "strong0"
				   "strong1" "supply" "supply0" "supply1" "time" "tran" "tranif0" "tranif1" "tri" "tri0" "tri1" "triand"
				   "trior" "trireg" "unsigned" "uwire" "vectored" "wand" "weak0" "weak1" "wire" "wor" "xnor" "xor"
				   "bit" "byte" "chandle" "const" "enum" "int" "logic" "longint" "packed" "ref" "shortint" "shortreal"
				   "static" "string" "struct" "type" "typedef" "union" "var" "interconnect" "nettype" "above" "abs"
				   "absdelay" "abstol" "ac_stim" "access" "acos" "acosh" "aliasparam"
				   "analog" "analysis" "asin" "asinh" "atan" "atan2" "atanh" "branch" "ceil" "connect"
				   "connectmodule" "connectrules" "continuous" "cos" "cosh" "ddt" "ddt_nature" "ddx" "discipline"
				   "discrete" "domain" "driver_update" "endconnectmodule" "endconnectrules" "enddiscipline"
				   "endnature" "endparamset" "exclude" "exp" "final_step" "flicker_noise" "floor" "flow"
				   "from" "ground" "hypot" "idt" "idt_nature" "idtmod" "inf" "initial_step" "laplace_nd"
				   "laplace_np" "laplace_zd" "laplace_zp" "last_crossing" "limexp" "ln" "log" "max"
				   "merged" "min" "nature" "net_resolution" "noise_table" "paramset" "potential"
				   "pow" "resolveto" "sin" "sinh" "slew" "split" "sqrt" "tan" "tanh" "timer"
				   "transition" "units" "white_noise" "wreal" "zi_nd" "zi_np" "zi_zd" "zi_zp"
				   "always" "assign" "automatic" "case" "casex" "casez" "cell" "config" "deassign"
				   "default" "design" "disable" "edge" "else" "endcase" "endconfig" "endfunction"
				   "endgenerate" "endmodule" "endprimitive" "endspecify" "endtable" "endtask" "for"
				   "force" "forever" "fork" "function" "generate" "if" "ifnone" "incdir" "include"
				   "initial" "instance" "join" "large" "liblist" "library" "macromodule" "medium"
				   "module" "negedge" "noshowcancelled" "posedge" "primitive" "pulsestyle_ondetect"
				   "pulsestyle_onevent" "release" "repeat" "scalared" "showcancelled" "small" "specify"
				   "strength" "table" "task" "use" "wait" "while" "alias" "always_comb" "always_ff"
				   "always_latch" "assert" "assume" "analog" "before" "bind" "bins" "binsof" "break"
				   "class" "clocking" "constraint" "context" "continue" "cover" "covergroup" "coverpoint"
				   "cross" "dist" "do" "endclass" "endclocking" "endgroup" "endinterface" "endpackage"
				   "endprogram" "endproperty" "endsequence" "expect" "export" "extends" "extern" "final"
				   "first_match" "foreach" "forkjoin" "iff" "ignore_bins" "illegal_bins" "import" "inside"
				   "interface" "intersect" "join_any" "join_none" "local" "matches" "modport" "new" "null"
				   "package" "priority" "program" "property" "protected" "pure" "rand" "randc" "randcase"
				   "randsequence" "return" "sequence" "solve" "super" "tagged" "this" "throughout" "timeprecision"
				   "timeunit" "unique" "virtual" "void" "wait_order" "wildcard" "with" "within" "accept_on"
				   "checker" "endchecker" "eventually" "global" "implies" "let" "nexttime" "reject_on" "restrict"
				   "s_always" "s_eventually" "s_nexttime" "s_until" "s_until_with" "strong" "sync_accept_on"
				   "sync_reject_on" "unique0" "until" "until_with" "untyped" "weak" "implements" "soft" "begin" "end")))


(use-package xah-fly-keys
  :disabled
  :config (xah-fly-keys-set-layout "qwerty"))

(use-package lsp-mode
  :disabled
  :config
  (add-to-list 'lsp-language-id-configuration '(verilog-mode . "verilog"))
  (lsp-register-client
   (make-lsp-client :new-connection (lsp-stdio-connection "verible-verilog-ls")
                    :major-modes '(verilog-mode)
                    :server-id 'verible-ls))

  :hook (verilog-mode . lsp))
