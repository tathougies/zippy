;; Emacs major mode for the Zephyr query language

(setq zephyr-syntax
      `(
	( ,(regexp-opt '("DEFINE" "PACKAGE" "EXPORT" "DATA") 'word) . font-lock-keyword-face )
	( ,(regexp-opt '("SWAP" "DUP" "ZAP" "CAT" "UNCONS" "CONS" "I" "DIP" "ZIP-UP" "ZIP-DOWN" "CUR-TAG" "CUR-ATOM" "IFTE" "+" "==" "FAIL" "LENGTH" "ARG-HOLE" "ZIP-REPLACE") 'word) . font-lock-builtin-face )
	( "[0-9]+" . font-lock-constant-face )
	( "\\\"(\\\\\\\"\\|[^\\\"])*\\\"" . font-lock-string-literal-face )
	))

(defvar zephyr-syntax-table nil "syntax table for zephyr-mode")
(setq zephyr-syntax-table
      (let ((syn-table (make-syntax-table)))
	(modify-syntax-entry ?{ "< b" syn-table)
	(modify-syntax-entry ?} "> b" syn-table)
	syn-table))

(define-derived-mode zephyr-mode fundamental-mode
  "zephyr-mode is an emacs major mode for editing the Zephyr query language"
  :syntax-table zephyr-syntax-table
  (setq font-lock-defaults '(zephyr-syntax))
  (setq mode-name "zephyr"))
