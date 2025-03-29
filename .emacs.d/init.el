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
             

;; Vterm configuration
(use-package vterm
  :config 
  (setq vterm-max-scrollback 10000)
  (setq-local display-line-numbers nil)

  :bind 
    (:map vterm-mode-map
       ("C-y" . vterm-yank) 
    )
  :hook 
  ; disable showing of columns/row number in terminal
  (vterm-mode . (lambda() (display-line-numbers-mode -1))) 
  (vterm-mode . (lambda() (line-number-mode -1)))
  (vterm-mode . (lambda() (column-number-mode -1)))
)

(straight-use-package 'org)

; not really sure if this is needed with straight
(use-package auto-package-update
   :ensure t
   :config
   (setq auto-package-update-delete-old-versions t
         auto-package-update-interval 4)
   (auto-package-update-maybe)
)





; load as soon as possible.
; avoids emacs generating littering files all over the place.
(use-package no-littering
  :ensure t
  :config
  (setq 
      backup-by-copying t
      backup-directory-alist '(("." . "~/.emacs.d/emacs_backup_saves/")) 
      delete-old-versions t
      kept-new-versions 10
      kept-old-versions 10
      version-control t
      auto-save-file-name-transforms
        `((".*" , (no-littering-expand-var-file-name "auto-save/") t))
  )
)

;modus themes need to be loaded as soon as possible.
;then load one of them with use-package emacs, if this theme is desired
(use-package modus-themes
  :init
  (setq
    modus-themes-common-palette-overrides '( 
      (comment yellow-cooler)
      ;(string green-cooler)
      (bg-paren-match bg-magenta-intense)
      (bg-region bg-ochre) ; try to replace `bg-ochre' with `bg-lavender', `bg-sage'
      (fg-region unspecified)
    )
    modus-themes-italic-constructs t
  )
  :config
  ;; Load the theme of your choice:
  ;(load-theme 'modus-vivendi :noconfirm)
  :bind ("<f5>" . modus-themes-toggle))

; emacs base config
(use-package emacs
  :init
  (setq 
    inhibit-startup-screen t
    column-number-mode t ; show column number
    line-number-mode t ; show line number
    indent-tabs-mode nil ; always use spaces, not tabs
    enable-recursive-minibuffers t
    compilation-scroll-output t
    compilation-always-kill t
    ;make-backup-files nil "Do not make backup files on save buffer."
    ;auto-save-default nil "Do not auto-save of every file-visiting buffer."
    create-lockfiles  nil ;Do not use lock-files.
    require-final-newline t ;Ends file with a newline.
    visible-bell -1 ; avoid annoying sounds

      ; in M-x, hide commands that do not work in the current mode
    read-extended-command-predicate #'command-completion-default-include-p 
  )
  ; find undo management if needed
  ;and package to manage selection of words...
  (show-paren-mode t)
  (global-display-line-numbers-mode 0)
  (tool-bar-mode -1)

  ; Font setup  
  (cond
   ((find-font (font-spec :name "Fira Code"))
    (set-frame-font "Fira Code 14" nil t)))

  :bind
  ("C-c C-q" . comment-or-uncomment-region)
  ("M-*" . pop-tag-mark)
  ("C-M-\\" . indent-region)
  
  :config
  :hook
  (prog-mode . display-line-numbers-mode)
  (fundamental-mode . display-line-numbers-mode)
  (text-mode . display-line-numbers-mode)
)

; manage recent opened files
(use-package recentf
  :after no-littering
  :custom
  (add-to-list 'recentf-exclude no-littering-var-directory)
  (add-to-list 'recentf-exclude no-littering-etc-directory)
  (recentf-mode)
)

; mode to open very large files
(use-package vlf
  :init
  (require 'vlf-setup)
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
  :hook
  (prog-mode . smartparens-mode)
)

; navigate and highlight keywords in the code
(use-package symbol-overlay
  :ensure t
  :bind
  ("M-i"  . symbol-overlay-put)
  ("M-n"  . symbol-overlay-switch-forward)
  ("M-p"  . symbol-overlay-switch-backward)
  ("<f7>" . symbol-overlay-mode)
  ("<f9>" . symbol-overlay-remove-all)
  :hook 
  (prog-mode . symbol-overlay-mode)
)

; smart white space trimmer 
(use-package ws-butler
  :ensure t
  :hook 
  (prog-mode . ws-butler-mode)
)

; template system for coding.
(use-package yasnippet
  :ensure t
  :init
  ; snippet folder
  (setq yas-snippet-dirs '("~/.emacs.d/snippets"))
  (yas-global-mode 1)
)

(use-package flycheck
  :ensure t
  :hook
  (cperl-mode-hook . flycheck-mode)

)

; highlight indentation.
; not really used anymore
(use-package highlight-indent-guides
  :config
  (setq highlight-indent-guides-method 'bitmap
        highlight-indent-guides-responsive 'stack
        highlight-indent-guides-auto-character-face-perc 30
        highlight-indent-guides-delay 0.25))

; highlight indentation. This one I like it more.
(use-package indent-bars
  :straight 
  (indent-bars :type git :host github :repo "jdtsmith/indent-bars")
  :hook
  ((python-mode yaml-mode verilog-mode) . indent-bars-mode)  
)

;; vertico
;; Enable vertico
(use-package vertico
  :straight 
  (vertico 
    :files (:defaults "extensions/*")
    :includes (vertico-mouse vertico-directory)
  )

  :init
  (vertico-mode)
  (vertico-mouse-mode)

  :bind 
  (:map vertico-map
    ("<tab>" . vertico-directory-enter)
    ("\t" . vertico-directory-enter) ; \t or \r
    ("\d" . vertico-directory-delete-char)
    ("\M-\d" . vertico-directory-delete-word))
  :hook
  (rfn-eshadow-update-overlay . vertico-directory-tidy)
)

; orderless
; complex to understand how to setup and what I want
(use-package orderless
  :init
  ;; Configure a custom style dispatcher (see the Consult wiki)
  ;; (setq orderless-style-dispatchers '(+orderless-dispatch)
  ;;       orderless-component-separator #'orderless-escapable-split-on-space)
  (setq 
    completion-styles '(orderless)
    completion-category-defaults nil
    completion-category-overrides '((file (styles partial-completion)))
  )
)

;; Enable rich annotations using the Marginalia package
(use-package marginalia
  ;; Either bind `marginalia-cycle' globally or only in the minibuffer
  :bind 
  (:map minibuffer-local-map
    ("M-A" . marginalia-cycle)
  )
  :init
  (marginalia-mode)
)

;; Example configuration for Consult
(use-package consult
  ;; Replace bindings. Lazily loaded due by `use-package'.
  :bind (;; C-c bindings (mode-specific-map)
    ("C-s" . consult-line)
    ;check these ones below
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
      ("M-r" . consult-history)                 ;; orig. previous-matching-history-element
  )                

  ;; Enable automatic preview at point in the *Completions* buffer. This is
  ;; relevant when you use the default completion UI.
  :hook (completion-list-mode . consult-preview-at-point-mode)

  ;; The :init configuration is always executed (Not lazy)
  :init
  ;; Optionally configure the register formatting. This improves the register
  ;; preview for `consult-register', `consult-register-load',
  ;; `consult-register-store' and the Emacs built-ins.
  (setq 
    register-preview-delay 0.5
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
   :preview-key '(:debounce 0.4 any)
  )

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
  ("C-." . embark-act)         ;; pick some comfortable binding
  ("C-;" . embark-dwim)        ;; good alternative: M-.
  ("C-h B" . embark-bindings) ;; alternative for `describe-bindings'
   
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
  :straight 
  (corfu 
    :files (:defaults "extensions/*")
    :includes (corfu-info corfu-history corfu-popupinfo))
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

  (corfu-popupinfo-delay 0.25)

  :bind 
    ("M-/" . completion-at-point)
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
      ("C-SPC" . corfu-insert-separator)
    )
  
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

(use-package svg-lib)

(use-package kind-icon
  :after corfu
  ;:disabled
  :custom
  (kind-icon-use-icons t)
  (kind-icon-default-face 'corfu-default) ; Have background color be the same as `corfu' face background
  (kind-icon-blend-background t)  ; Use midpoint color between foreground and background colors ("blended")?
  (kind-icon-blend-frac 0.08)
  (kind-icon-default-style
    '(:padding 0 :stroke 0 :margin -1 :radius 0 :height 0.5 :scale 1.0))

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
  (add-hook 'kb/themes-hooks #'(lambda () (interactive) (kind-icon-reset-cache)))
)

(use-package cape
  :straight 
  (cape 
    :files (:defaults "*")
    :includes (cape-keyword cape-char))

  ;; Bind dedicated completion commands
  ;; Alternative prefix keys: C-c p, M-p, M-+, ...
  :bind 
  ("C-c p p" . completion-at-point) ;; capf
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
  ("C-c p r" . cape-rfc1345)

  :init
  ;; Add `completion-at-point-functions', used by `completion-at-point'.
  ;(add-to-list 'completion-at-point-functions #'cape-dabbrev)
  (add-to-list 'completion-at-point-functions #'cape-file)
  ;;(add-to-list 'completion-at-point-functions #'cape-history)
  (add-to-list 'completion-at-point-functions #'cape-keyword)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-tex)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-sgml)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-rfc1345)
  (add-to-list 'completion-at-point-functions #'cape-ispell)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-dict)
  (add-to-list 'completion-at-point-functions #'cape-symbol)
  ;; ;;(add-to-list 'completion-at-point-functions #'cape-line)

  (setq cape-dabbrev-check-other-buffers 'some)

  ; add as hook because of verilog-mode replacing locally completion functions.
  :hook
  (verilog-mode . 
    (lambda()
                                        ;(delete t completion-at-point-functions)
      (add-to-list 'completion-at-point-functions #'cape-keyword)
      (add-to-list 'completion-at-point-functions #'cape-file)
      (add-to-list 'completion-at-point-functions #'cape-dabbrev)))
)

; project management. 
(use-package projectile
  :ensure t
  :init
  (projectile-mode +1)
  :bind 
  (:map projectile-mode-map
    ("s-p" . projectile-command-map)
    ("C-c j" . projectile-command-map)
  )
)

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
    citre-readtags-program "~/bin/readtags"
    citre-ctags-program "~bin/ctags"
    ;; Set these if gtags/global is not in your PATH (and you want to use the
    ;; global backend)
    citre-gtags-program "~/bin/gtags"
    citre-global-program "~/bin/global"
    ;; Set this if you use project management plugin like projectile.  It's
    ;; used for things like displaying paths relatively, see its docstring.
    citre-project-root-function #'projectile-project-root
    ;; Set this if you want to always use one location to create a tags file.
    citre-default-create-tags-file-location 'global-cache
    ;; See the "Create tags file" section above to know these options
    citre-use-project-root-when-creating-tags nil
    citre-prompt-language-for-ctags-command nil
    ;; By default, when you open any file, and a tags file can be found for it,
    ;; `citre-mode' is automatically enabled.  If you only want this to work for
    ;; certain modes (like `prog-mode'), set it like this.
    citre-auto-enable-citre-mode-modes '(prog-mode)
  )
  :bind 
    (:map citre-mode-map
      ("M-." . citre-jump)
      ("M-*" . citre-jump-back)
      ("C-M-." . citre-peek)
      ;("M-/" . citre-ace-peek)
      ("C-x c u" . citre-update-this-tags-file)
    )
)


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
  (add-hook 'kill-emacs-hook 
    #'(lambda nil
      (bm-buffer-save-all)
      (bm-repository-save)
    )
  )

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

  :bind (
    ("<f2>" . bm-next)
    ("S-<f2>" . bm-previous)
    ("C-<f2>" . bm-toggle)
  )
)

; TODO include this in the emacs base config
(add-hook 'prog-mode-hook 'hs-minor-mode)

(use-package verilog-mode
  :mode 
  ("\\.vae?" . verilog-mode)
  ("\\.vams" . verilog-mode)

  :config
  (setq
    verilog-indent-spaces             3 
    verilog-indent-level              verilog-indent-spaces
    verilog-indent-level-module       verilog-indent-spaces
    verilog-indent-level-declaration  verilog-indent-spaces
    verilog-indent-level-behavioral   verilog-indent-spaces
    verilog-indent-level-directive    1
    verilog-case-indent               verilog-indent-spaces
    verilog-auto-newline              'nil
    verilog-auto-indent-on-newline    t
    verilog-tab-always-indent         t
    verilog-auto-endcomments          t
    verilog-minimum-comment-distance  10
    verilog-indent-begin-after-if     'nil
    verilog-indent-lists              'nil ; 'nil
    verilog-auto-lineup               'all;'declarations)
    verilog-align-ifelse              t
    verilog-highlight-p1800-keywords  t
    verilog-indent-declaration-macros t
  )

  ; function I wrote to highlight nice things not highlighted by default.
  (defun verilog-extend-font-lock ()
    (font-lock-add-keywords nil '(
      ; Valid hex number (will highlight invalid suffix though)
      ("'[b o h d][[:xdigit:]]+\\b" . font-lock-warning-face)

      ; number
      ("\\b[0-9]+\\b" . font-lock-string-face)

      ;negations symbols
      ("\\(\\[~]\\)\\|\\(\\!=*\\)" . font-lock-warning-face)

      ; operation symbols and commas
      ("[+=<>%\\*/:&^\\|;,.-]" . font-lock-type-face)

      ;highlight things inside parenthesis []
      ("\\[\s*\\([$]\\|[[:alnum:]]+\\)\s*\\]" 1 font-lock-builtin-face)
      ;highlight #(thing) even if attached to a word.
      ;example uvm_config_db#(uvm_bitstream_t)
      ("#([a-z_A-Z0-9]+)?" . font-lock-type-face))))
  :bind (
    :map verilog-mode-map
      ("C-{" . verilog-beg-of-defun)
      ("C-}" . verilog-end-of-defun)
  )
  :hook (verilog-mode . verilog-extend-font-lock)
)

; I do not like this. Disabled.
(use-package cperl-mode
  :disabled
  ;:ensure t
  :init ; maybe put hook in init?
  :mode ("\.pl$" . cperl-mode)
  :config
  ;; cperl-mode
  (setq cperl-indent-level 4
        cperl-highlight-variables-indiscriminately t
        cperl-electric-parens nil ; below this there are things from internet. check them
        cperl-continued-statement-offset 4
        cperl-close-paren-offset -4
        cperl-label-offset -4
        cperl-comment-column 40
        cperl-indent-parens-as-block t
        cperl-tab-always-indent nil
        cperl-font-lock t)
  (cperl-set-style "PerlStyle")
  :hook
  (smartparens-enabled-hook . (lambda() (define-key cperl-mode-map "{" nil)))
  (smartparens-disabled-hook . (lambda() (define-key cperl-mode-map "{" 'cperl-electric-lbrace))))

; these have to be improved; maybe use only font lock without indentation...
;(add-to-list 'auto-mode-alist '("\\.f" . verilog-mode))
;(add-to-list 'auto-mode-alist '("\\.vsif[h]" . c-mode))

(use-package emacs ; without this operandi theme is loaded.
  :init
  :config
  ;; Load the theme of your choice.
  (load-theme 'modus-vivendi :noconfirm))

;;; doom modeline
;; probably I could spend a little time to customize better the modeline
(use-package doom-modeline
  :ensure t
  :init (doom-modeline-mode 1)
)
;; (use-package doom-modeline
;;   :hook (after-init . doom-modeline-mode)
;;   :custom
;;   (doom-modeline-height 25)
;;   (doom-modeline-bar-width 1)
;;   (doom-modeline-icon nil)
;;   (doom-modeline-window-width-limit nil)
;;   (doom-modeline-major-mode-icon nil)
;;   (doom-modeline-major-mode-color-icon nil)
;;   (doom-modeline-buffer-file-name-style 'auto)
;;   (doom-modeline-buffer-state-icon nil)
;;   (doom-modeline-buffer-modification-icon nil)
;;   (doom-modeline-minor-modes nil)
;;   (doom-modeline-enable-word-count nil)
;;   (doom-modeline-buffer-encoding nil)
;;   (doom-modeline-modal t)
;;   (doom-modeline-indent-info nil)
;;   (doom-modeline-checker-simple-format t)
;;   (doom-modeline-vcs-max-length 12)
;;   (doom-modeline-env-version nil)
;;   (doom-modeline-irc-stylize 'identity)
;;   (doom-modeline-github-timer nil)
;;   (doom-modeline-gnus-timer nil))

(use-package shrink-whitespace
  :ensure t
  :bind
  ("M-\\" . shrink-whitespace))

(use-package all-the-icons
  :ensure t
  :config
  (setq bdf-directory-list '("~/.emacs.d/fonts/"))
;; Use 'prepend for the NS and Mac ports or Emacs will crash.
  (set-fontset-font t 'unicode (font-spec :family "all-the-icons") nil 'append)
  (set-fontset-font t 'unicode (font-spec :family "file-icons") nil 'append)
  (set-fontset-font t 'unicode (font-spec :family "Material Icons") nil 'append)
  (set-fontset-font t 'unicode (font-spec :family "github-octicons") nil 'append)
  (set-fontset-font t 'unicode (font-spec :family "FontAwesome") nil 'append)
  (set-fontset-font t 'unicode (font-spec :family "Weather Icons") nil 'append))

(use-package all-the-icons-completion
  :after (all-the-icons marginalia)
  :ensure t
  :init
  (all-the-icons-completion-mode)
  :hook
  (marginalia-mode-hook . all-the-icons-completion-marginalia-setup))


(use-package p4
  :ensure t)

(use-package stupid-indent-mode
  :init
  (setq stupid-indent-level 3)
  :hook
  (sh-mode-hook . (lambda() stupid-indent-mode 1)))

(use-package which-func
  :config
  (setq which-func-unknown "Global")
  :custom
  (which-function-mode 1))

; ♬ if  only I could be so grossly incandescent ♬
(use-package solaire-mode
  :ensure t
  :hook 
  (after-init . solaire-global-mode))

(use-package golden-ratio
  :ensure t
  :after ace-window
  :hook
  (after-init . golden-ratio-mode)
  :config
  (add-to-list 'golden-ratio-extra-commands 'ace-window))

(use-package format-all
  :commands format-all-mode
  :hook
  (prog-mode . format-all-mode)
  :config
  (setq-default format-all-formatters 
    '(("C" (astyle "--mode-c"))
    ("Shell" (shfmt "-i" "4" "-ci"))))
)

(defun init-file-open ()
  (interactive)
  (find-file "~/.emacs.d/init.el"))

(defun show-file-name ()
  "Show the full path file in the minibuffer"
  (interactive)
  (message (buffer-file-name)))

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



(use-package ligature
  :load-path "path-to-ligature-repo"
  :config
  ;; Enable the "www" ligature in every possible major mode
  (ligature-set-ligatures 't '("www"))

  (ligature-set-ligatures 'prog-mode '("www" "**" "***" "**/" "*>" "*/" "\\\\" "\\\\\\" "{-" "::"
                                     ":::" ":=" "!!" "!=" "!==" "-}" "----" "-->" "->" "->>"
                                     "-<" "-<<" "-~" "#{" "#[" "##" "###" "####" "#(" "#?" "#_"
                                     "#_(" ".-" ".=" ".." "..<" "..." "?=" "??" ";;" "/*" "/**"
                                     "/=" "/==" "/>" "//" "///" "&&" "||" "||=" "|=" "|>" "^=" "$>"
                                     "++" "+++" "+>" "=:=" "==" "===" "==>" "=>" "=>>" "<="
                                     "=<<" "=/=" ">-" ">=" ">=>" ">>" ">>-" ">>=" ">>>" "<*"
                                     "<*>" "<|" "<|>" "<$" "<$>" "<!--" "<-" "<--" "<->" "<+"
                                     "<+>" "<=" "<==" "<=>" "<=<" "<>" "<<" "<<-" "<<=" "<<<"
                                     "<~" "<~~" "</" "</>" "~@" "~-" "~>" "~~" "~~>" "%%"
                                     "|->" "|=>"))

  (ligature-set-ligatures 'vterm-mode '("www" "**" "***" "**/" "*>" "*/" "\\\\" "\\\\\\" "{-" "::"
                                        ":::" ":=" "!!" "!=" "!==" "-}" "----" "-->" "->" "->>"
                                        "-<" "-<<" "-~" "#{" "#[" "##" "###" "####" "#(" "#?" "#_"
                                        "#_(" ".-" ".=" ".." "..<" "..." "?=" "??" ";;" "/*" "/**"
                                        "/=" "/==" "/>" "//" "///" "&&" "||" "||=" "|=" "|>" "^=" "$>"
                                        "++" "+++" "+>" "=:=" "==" "===" "==>" "=>" "=>>" "<="
                                        "=<<" "=/=" ">-" ">=" ">=>" ">>" ">>-" ">>=" ">>>" "<*"
                                        "<*>" "<|" "<|>" "<$" "<$>" "<!--" "<-" "<--" "<->" "<+"
                                        "<+>" "<=" "<==" "<=>" "<=<" "<>" "<<" "<<-" "<<=" "<<<"
                                        "<~" "<~~" "</" "</>" "~@" "~-" "~>" "~~" "~~>" "%%"
                                        "|->" "|=>"))
  (global-ligature-mode t))

(use-package desktop
  :ensure nil
  :config
  (desktop-save-mode 0))

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

; Automatically switch to ts-mode for major mode, if available
(use-package treesit-auto
  :demand t
  :config 
  (global-treesit-auto-mode))

;; (use-package verilog-ext
;;  :straight (:host github :repo "gmlarumbe/verilog-ext")
;;  :after verilog-mode
;;  :hook ((verilog-mode . verilog-ext-which-func)
;;         (verilog-mode . verilog-ext-hs-setup))
;;  ;:config (verilog-ext-mode-setup)
;;  )

(use-package verilog-ext
  :after verilog-mode
  :demand
  :hook 
  (verilog-mode . verilog-ext-mode)
  :init
  (setq 
    verilog-ext-feature-list '(
      font-lock 
      xref 
      capf
      hierarchy 
      eglot 
      lsp 
      flycheck
      beautify
      navigation
      template
      formatter
      compilation
      imenu
      which-func
      hideshow
      typedefs
      time-stamp
      block-end-comments
      company-keywords
      ports
    )
  )
  :config 
  (verilog-ext-mode-setup)
)

(use-package verilog-ts-mode
  :mode 
  ("\\.vae?" . verilog-ts-mode)
  ("\\.vams" . verilog-ts-mode)

  :config
  (setq
    verilog-ts-indent-spaces 3
    verilog-ts-indent-level verilog-indent-spaces
    verilog-ts-indent-level-module verilog-indent-spaces
    verilog-ts-indent-level-declaration verilog-indent-spaces
    verilog-ts-indent-level-behavioral verilog-indent-spaces
    verilog-ts-indent-level-directive 1
    verilog-ts-case-indent verilog-indent-spaces
    verilog-ts-auto-newline 'nil
    verilog-ts-auto-indent-on-newline t
    verilog-ts-tab-always-indent t
    verilog-ts-auto-endcomments t
    verilog-ts-minimum-comment-distance 10
    verilog-ts-indent-begin-after-if 'nil
    verilog-ts-indent-lists 'nil
    verilog-ts-auto-lineup 'all
    verilog-ts-align-ifelse t
    verilog-ts-highlight-p1800-keywords t
    verilog-ts-indent-declaration-macros t)
)

(use-package slime
  :init
    (setq inferior-lisp-program "sbcl.exe"))

(use-package fpga
  :mode (("\\.vsifh?\\'" . fpga-cadence-vsif-mode)))

(use-package spice-mode
  :mode (("\\.sp" . spice-mode)))

(use-package spectre-mode
  :mode (("\\.scs" . spectre-mode)))

(use-package skill-mode
  :straight (skill :type git :host github :repo "Aurelbuche/skill-mode"))

(use-package wavedrom-mode
  :config
  (setq 
    wavedrom-output-format "png"
    wavedrom-output-directory "~/wavedrom"
  )
  (set-face-attribute 'wavedrom-font-lock-brackets-face-nil :foreground "goldenrod" nil)
  (set-face-attribute 'wavedrom-font-lock-punctuation-face nil :foreground "burlywood" nil)
)

(use-package yasnippet-snippets)

(straight-use-package 'tree-sitter)
(straight-use-package 'tree-sitter-langs)
(require 'tree-sitter)
(require 'tree-sitter-langs)

(use-package apheleia)

(use-package org
  :ensure t
  :config
  (setq 
    org-log-done 'time
    org-startup-indented t))

(use-package org-modern
  :ensure t
  :init (global-org-modern-mode))


(use-package graphviz-dot-mode)

(use-package dirvish
  :config
  (setq dirvish-attributes '(
    vc-state
    subtree-state
    all-the-icons
    collapse
    git-msg
    file-time
    file-size
    )
  (dirvish-override-dired-mode)
  )
)

(use-package logview)

;; (use-package excorporate)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; things not really useful, but fun
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(use-package poke-line
  :ensure t
  :config
  (poke-line-global-mode 1)
  (setq-default poke-line-pokemon "blaziken"))

(use-package nyan-mode
  :config
  (nyan-mode -1)
  (setq nyan-animate-nyancat t)
  (setq nyan-wavy-trail t)
) 

(use-package mega-zone
  :straight (mega-zone :type git :host github :repo "twitchy-ears/mega-zone")
  :after zone
  :config 
  (mega-zone-setup t)
  (setq mega-zone-dispatch-action 'zone-all)
)

(use-package zone-nyan
  :ensure t
  :config
  ;(setq zone-programs [zone-nyan])
)

(use-package zone-matrix
  :config
)

(use-package zone-rainbow
  :ensure t
  :after zone
  :config
  (setq zone-programs (vconcat [zone-rainbow] zone-programs))
  (setq zone-programs [zone-rainbow])
  (zone-when-idle 300)
)

(use-package fireplace)

;(setq zone-programs [zone-matrix])

(use-package minesweeper)
(use-package 2048-game)
(use-package gnugo)
(use-package xkcd)
(use-package pacmacs)
(use-package selectric-mode)

(use-package clippy
  :config
  (setq clippy-tip-show-function #'clippy-popup-tip-show))

(use-package parrot
  :config
  (setq parrot-num-rotations nil)
  (parrot-mode)
  (parrot-start-animation))

(use-package minimap)