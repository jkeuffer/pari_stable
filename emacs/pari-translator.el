;; This file is to be used with pari.el where further explanations
;; may be found. See also the file pariemacs.txt.
;; Should be accompanied by the file with-syntax.el. This latter
;; contains an example as to how to write a "translating" file.

;; Created November 22 1998 by Olivier Ramare (ramare@gat.univ-lille1.fr)

;; It contains functions used for writing translating eLisp-modules
;; that translate a program given in a langage into something comprehensible
;; by the gp calculator.

;; Add
;; /*@ (load-file "Name-of-the-translating-file")
;;     (setq gp-input-filter-hook (list 'translate)) */
;; to the file to translate. 'translate is the translation function.
;; The file has to be currently edited for this command to be taken
;; into account.
;; 
;; The first command of 'translate is either
;;    (gp-translate-on-other-file) and the file to be translated
;;                                 will not be changed.
;;    (gp-translate-on-same-file) and the file to be translated
;;                                will be actually changed.

(provide 'pari-translator)

(defun gp-translate-on-other-file nil
  "This function contains the command that should be executed
to translate a file onto another one. The file to translate is in the
currently editted (and set) buffer. The translated file is editted in
another buffer which is the selected one at the end of this command."

  (goto-char (point-min))
  (get-buffer-create "*translation*")
  (save-excursion (set-buffer "*translation*") (erase-buffer))
  (copy-to-buffer "*translation*" (point-min) (point-max))
  (set-buffer "*translation*")
  ;; 'gp-temp-file is a variable of pari.el:
  (set-visited-file-name gp-temp-file t)
  ;; The preceding function has changed the buffer-name!
  (rename-buffer "*translation*")

  ;; To limit the translation to this file:
  (setq gp-input-filter-hook nil))

(defun gp-translate-on-same-file nil
  "This function contains the command that should be executed
to translate a file onto another one. The file to translate is in the
currently editted (and set) buffer."

  (goto-char (point-min))

  ;; To limit the translation to this file:
  (setq gp-input-filter-hook nil))


;;--------------------
;; Expression finders
;;--------------------

;; An inner full expression in gp is one of these two:
;; fn-call :: identifier(...matching-)
;; identifier
;; preceded and followed by any number of comments, spaces, newline
;; or tabulation-character.
;; Its end delimitation is "," or ";" or "}"
;; Thus, we do not detect full expression located at the end of
;; a one line function definition, not surrounded by "{}",
;; not followed by ";"

;; pari.el already contains 'gp-find-comment, 'gp-find-global-var
;; and 'gp-search-forward-string-delimiter.

(defconst gp-regexp-identifier  "[a-zA-Z_][a-zA-Z_0-9]*"
"Regexp to match identifiers in gp.")

(defconst gp-regexp-comment "\\\\\\\\$\\|/\\*\\([^\\*]\\|\\*[^/]\\)*\\*/"
"Regexp to match comments in gp")

(defun gp-looking-at-identifierp nil
"T if point is located at the beginning of a gp-identifier."
  (if (looking-at gp-regexp-identifier)
      (if (bobp)
          t
          (save-excursion
            (forward-char -1)
            (looking-at "[^a-zA-Z_0-9]")))
      nil))

(defun gp-looking-at-identifier nil
"Return end of identifier if gp-looking-at-identifier is T,
nil otherwise."
  (if (gp-looking-at-identifierp)
      (save-excursion (skip-chars-forward "a-zA-Z_0-9") (point))
      nil))

(defun gp-looking-at-fn-call nil
"Return end of fn-call if point is located at the beginning of a
fn-call, and nil otherwise."
  (if (gp-looking-at-identifierp)
      (save-excursion
        (goto-char (gp-looking-at-identifier))
        (if (not (looking-at "[ \t\n\\\\]*("))
            nil
            (goto-char (- (match-end 0) 1))
            (forward-sexp)  ;; Error if expression is unbalanced.
            (point)))
      nil))

(defun gp-skip-comments nil
  (while (looking-at gp-regexp-comment)
         (goto-char (match-end 0))))

(defun gp-looking-at-term nil
"Return end of term if point is located at the beginning of a
fn-call, and nil otherwise.
  A `term' is either an identifier, either a fn-call, surrounded by
any number of parenthesis/space/newline/tab-char/backslash. It may
also start by a comment."
  (gp-skip-comments)
  (if (looking-at "[ \t\n\\\\]*(")
      (let ((p-end (save-excursion
                     (forward-sexp)
                     (gp-skip-comments)
                     (point))))
           (forward-char 1)
           (if (gp-looking-at-term) p-end nil))
      (let ((p-end (gp-looking-at-fn-call)))
           (if p-end p-end
               (if (gp-looking-at-identifierp)
                   (gp-looking-at-identifier)
                   nil)))))

(defun gp-looking-at-rat-exp nil
"Return end of rational expression if point is located at the beginning
of one, nil otherwise.
  A rational expression for gp is a succession of terms separated by one
of the operators +-*%/."
  (save-excursion
    (let ((first-term (gp-looking-at-term)))
         (if (not first-term)
             nil
             (goto-char first-term)
             (if (looking-at "[ \t\n\\\\]*[+-*%/]")
                 (progn (goto-char (match-end 0))
                        (gp-looking-at-rat-exp))
                 first-term)))))

;; pari-translator.el ends here.
