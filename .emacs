(require 'package)
(let* ((no-ssl (and (memq system-type '(windows-nt ms-dos))
                    (not (gnutls-available-p))))
       (proto (if no-ssl "http" "https")))
  (add-to-list 'package-archives (cons "melpa" (concat proto "://melpa.org/packages/")) t))

(package-initialize)


(defun set-exec-path-from-shell-PATH ()
  (let ((path-from-shell (replace-regexp-in-string
                          "[ \t\n]*$"
                          ""
                          (shell-command-to-string "$SHELL --login -i -c 'echo $PATH'"))))
    (setenv "PATH" path-from-shell)
    (setq eshell-path-env path-from-shell) ; for eshell users
    (setq exec-path (split-string path-from-shell path-separator))))

(when window-system (set-exec-path-from-shell-PATH))

;; Shell at current window

(add-to-list 'display-buffer-alist
             `(,(rx bos "*shell*")
               display-buffer-same-window
               (reusable-frames . visible)))


;;; Nice size for the default window
(defun get-default-height ()
       (/ (- (display-pixel-height) 50)
          (frame-char-height)))

(add-to-list 'default-frame-alist '(width . 200))
(add-to-list 'default-frame-alist (cons 'height (get-default-height)))


(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(ansi-color-names-vector
   ["#212526" "#ff4b4b" "#b4fa70" "#fce94f" "#729fcf" "#e090d7" "#8cc4ff" "#eeeeec"])
 '(coq-maths-menu-enable t)
 '(coq-shortcut-alist nil)
 '(coq-token-symbol-map
   (quote
    (("alpha" "α")
     ("beta" "β")
     ("gamma" "γ")
     ("delta" "δ")
     ("epsilon" "ε")
     ("zeta" "ζ")
     ("eta" "η")
     ("theta" "θ")
     ("iota" "ι")
     ("kappa" "κ")
     ("lambda" "λ")
     ("mu" "μ")
     ("nu" "ν")
     ("xi" "ξ")
     ("pi" "π")
     ("rho" "ρ")
     ("sigma" "σ")
     ("tau" "τ")
     ("upsilon" "υ")
     ("phi" "ϕ")
     ("chi" "χ")
     ("psi" "ψ")
     ("omega" "ω")
     ("Gamma" "Γ")
     ("Delta" "Δ")
     ("Theta" "Θ")
     ("Lambda" "Λ")
     ("Xi" "Ξ")
     ("Pi" "Π")
     ("Sigma" "Σ")
     ("Upsilon" "Υ")
     ("Phi" "Φ")
     ("Psi" "Ψ")
     ("Omega" "Ω")
     ("forall" "∀")
     ("exists" "∃")
     ("nat" "ℕ" type)
     ("complex" "ℂ" type)
     ("real" "ℝ" type)
     ("int" "ℤ" type)
     ("rat" "ℚ" type)
     ("bool" "B" underline type)
     ("false" "false" bold sans)
     ("true" "true" bold sans)
     ("WHILE" "WHILE" bold sans)
     ("DO" "DO" bold sans)
     ("END" "END" bold sans)
     ("SKIP" "SKIP" bold sans)
     ("THEN" "THEN" bold sans)
     ("ELSE" "ELSE" bold sans)
     ("IFB" "IFB" bold sans)
     ("FI" "FI" bold sans)
     ("{{" "⦃" bold)
     ("}}" "⦄" bold)
     ("lhd" "⊲")
     ("rhd" "⊳")
     ("<=" "≤")
     (">=" "≥")
     ("=>" "⇒")
     ("->" "→")
     ("<-" "←")
     ("<->" "↔")
     ("++" "⧺")
     ("<<" "《")
     (">>" "》")
     ("===" "≡")
     ("=/=" "≢")
     ("=~=" "≅")
     ("==b" "≡")
     ("<>b" "≢")
     ("-->" "⟹-")
     ("++>" "⟹+")
     ("==>" "⟹")
     (":=" "≔")
     ("|-" "⊢")
     ("<>" "≠")
     ("-|" "⊣")
     ("\\/" "∨")
     ("/\\" "∧")
     ("~" "¬")
     ("============================" "⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯" bold tactical))))
 '(coq-unicode-tokens-enable t)
 '(custom-enabled-themes (quote (tsdh-dark)))
 '(package-selected-packages
   (quote
    (ensime ammonite-term-repl scala-mode texfrag px magic-latex-buffer ein command-log-mode company-coq proof-general projectile neotree)))
 '(proof-splash-enable nil))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 )

;; Auto-rename new eww buffers
(defun xah-rename-eww-hook ()
  "Rename eww browser's buffer so sites open in new page."
  (rename-buffer "eww" t))

(add-hook 'eww-mode-hook #'xah-rename-eww-hook)



(defun fix (to from)
  (save-excursion
   (goto-char (point-min))
   (while (search-forward from nil t)
     (replace-match to))))


(defun unifix ()
   "Fix unicode for Coq"
   (interactive)
     (fix "alpha" "α")
     (fix "beta" "β")
     (fix "gamma" "γ")
     (fix "delta" "δ")
     (fix "epsilon" "ε")
     (fix "zeta" "ζ")
     (fix "eta" "η")
     (fix "theta" "θ")
     (fix "iota" "ι")
     (fix "kappa" "κ")
     (fix "lambda" "λ")
     (fix "mu" "μ")
     (fix "nu" "ν")
     (fix "xi" "ξ")
     (fix "pi" "π")
     (fix "rho" "ρ")
     (fix "sigma" "σ")
     (fix "tau" "τ")
     (fix "upsilon" "υ")
     (fix "phi" "ϕ")
     (fix "chi" "χ")
     (fix "psi" "ψ")
     (fix "omega" "ω")
     (fix "Gamma" "Γ")
     (fix "Delta" "Δ")
     (fix "Theta" "Θ")
     (fix "Lambda" "Λ")
     (fix "Xi" "Ξ")
     (fix "Pi" "Π")
     (fix "Sigma" "Σ")
     (fix "Phi" "Φ")
     (fix "Psi" "Ψ")
     (fix "Omega" "Ω")
     (fix "forall " "∀")
     (fix "exists " "∃")
     (fix "nat" "ℕ")
     (fix "complex" "ℂ")
     (fix "real" "ℝ")
     (fix "int" "ℤ")
     (fix "rat" "ℚ")
     (fix "{{" "⦃")
     (fix "}}" "⦄")
     (fix "lhd" "⊲")
     (fix "rhd" "⊳")
     (fix "<=" "≤")
     (fix ">=" "≥")
     (fix "=>" "⇒")
     (fix "->" "→")
     (fix "<-" "←")
     (fix "<->" "↔")
     (fix "++" "⧺")
     (fix "<<" "《")
     (fix ">>" "》")
     (fix "===" "≡")
     (fix "=/=" "≢")
     (fix "=~=" "≅")
     (fix "==b" "≡")
     (fix "<>b" "≢")
     (fix "-->" "⟹-")
     (fix "++>" "⟹+")
     (fix "==>" "⟹")
     (fix ":=" "≔")
     (fix "|-" "⊢")
     (fix "<>" "≠")
     (fix "-|" "⊣")
     (fix "\\/" "∨")
     (fix "/\\" "∧")
     (fix "~" "¬")
     (fix "============================" "⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯"))


(load "~/.emacs.d/elpa/proof-general-20190531.2218/generic/proof-site.el")

(company-coq-mode)
;; Load company-coq when opening Coq files
(add-hook 'coq-mode-hook #'company-coq-mode)

(defun paste-unifix ()
  "paste and fix"
  (interactive)
  (yank)
  (unifix))

(defun mp-add-coq-keys ()
  (local-set-key (kbd "C-C f") 'unifix)
  (local-set-key (kbd "s-v") 'paste-unifix))

(add-hook 'coq-mode-hook 'mp-add-coq-keys)

(desktop-save-mode 1)
(require 'package)
(let* ((no-ssl (and (memq system-type '(windows-nt ms-dos))
                    (not (gnutls-available-p))))
       (proto (if no-ssl "http" "https")))
  (add-to-list 'package-archives (cons "melpa" (concat proto "://melpa.org/packages/")) t))

(package-initialize)


(defun set-exec-path-from-shell-PATH ()
  (let ((path-from-shell (replace-regexp-in-string
                          "[ \t\n]*$"
                          ""
                          (shell-command-to-string "$SHELL --login -i -c 'echo $PATH'"))))
    (setenv "PATH" path-from-shell)
    (setq eshell-path-env path-from-shell) ; for eshell users
    (setq exec-path (split-string path-from-shell path-separator))))

(when window-system (set-exec-path-from-shell-PATH))

;; Shell at current window

(add-to-list 'display-buffer-alist
             `(,(rx bos "*shell*")
               display-buffer-same-window
               (reusable-frames . visible)))


;;; Nice size for the default window
(defun get-default-height ()
       (/ (- (display-pixel-height) 50)
          (frame-char-height)))

(add-to-list 'default-frame-alist '(width . 200))
(add-to-list 'default-frame-alist (cons 'height (get-default-height)))





;; Auto-rename new eww buffers
(defun xah-rename-eww-hook ()
  "Rename eww browser's buffer so sites open in new page."
  (rename-buffer "eww" t))

(add-hook 'eww-mode-hook #'xah-rename-eww-hook)


;; Load company-coq when opening Coq files
(add-hook 'coq-mode-hook #'company-coq-mode)

(defun fix (to from)
  (save-excursion
   (goto-char (point-min))
   (while (search-forward from nil t)
     (replace-match to))))


(defun unifix ()
   "Fix unicode for Coq"
   (interactive)
     (fix "alpha" "α")
     (fix "beta" "β")
     (fix "gamma" "γ")
     (fix "delta" "δ")
     (fix "epsilon" "ε")
     (fix "zeta" "ζ")
     (fix "eta" "η")
     (fix "theta" "θ")
     (fix "iota" "ι")
     (fix "kappa" "κ")
     (fix "lambda" "λ")
     (fix "mu" "μ")
     (fix "nu" "ν")
     (fix "xi" "ξ")
     (fix "pi" "π")
     (fix "rho" "ρ")
     (fix "sigma" "σ")
     (fix "tau" "τ")
     (fix "upsilon" "υ")
     (fix "phi" "ϕ")
     (fix "chi" "χ")
     (fix "psi" "ψ")
     (fix "omega" "ω")
     (fix "Gamma" "Γ")
     (fix "Delta" "Δ")
     (fix "Theta" "Θ")
     (fix "Lambda" "Λ")
     (fix "Xi" "Ξ")
     (fix "Pi" "Π")
     (fix "Sigma" "Σ")
     (fix "Phi" "Φ")
     (fix "Psi" "Ψ")
     (fix "Omega" "Ω")
     (fix "forall " "∀")
     (fix "exists " "∃")
     (fix "nat" "ℕ")
     (fix "complex" "ℂ")
     (fix "real" "ℝ")
     (fix "int" "ℤ")
     (fix "rat" "ℚ")
     (fix "{{" "⦃")
     (fix "}}" "⦄")
     (fix "lhd" "⊲")
     (fix "rhd" "⊳")
     (fix "<=" "≤")
     (fix ">=" "≥")
     (fix "=>" "⇒")
     (fix "->" "→")
     (fix "<-" "←")
     (fix "<->" "↔")
     (fix "++" "⧺")
     (fix "<<" "《")
     (fix ">>" "》")
     (fix "===" "≡")
     (fix "=/=" "≢")
     (fix "=~=" "≅")
     (fix "==b" "≡")
     (fix "<>b" "≢")
     (fix "-->" "⟹-")
     (fix "++>" "⟹+")
     (fix "==>" "⟹")
     (fix ":=" "≔")
     (fix "|-" "⊢")
     (fix "<>" "≠")
     (fix "-|" "⊣")
     (fix "\\/" "∨")
     (fix "/\\" "∧")
     (fix "~" "¬")
     (fix "============================" "⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯⎯"))




(company-coq-mode)
;; Load company-coq when opening Coq files
(add-hook 'coq-mode-hook #'company-coq-mode)

(defun paste-unifix ()
  "paste and fix"
  (interactive)
  (yank)
  (unifix))

(defun mp-add-coq-keys ()
  (local-set-key (kbd "C-C f") 'unifix)
  (local-set-key (kbd "s-v") 'paste-unifix))

(add-hook 'coq-mode-hook 'mp-add-coq-keys)

(desktop-save-mode 1)
