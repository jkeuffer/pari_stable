;; This file is to be used with pari.el  and with pari-translator.el
;; where further explanations may be found. See also the file pariemacs.txt.

;; Created November 22 1998 by Olivier Ramare (ramare@gat.univ-lille1.fr)

;; Description:
;; A lisp file used in gp-script-mode to use the syntax 'with'.
;; See the function 'translate-with for more details.
;; To use it in an edited gp-program, introduce the following
;; lines in this program:
;; /*@
;; (load-file "with-syntax.el")
;; (setq gp-input-filter-hook (list 'translate))
;; */

;; You should load some general functions for translating,
;; and the name below may be different on your system:
(require 'pari-translator
  (concat gp-gphelp-dir "pari-translator.el"))

;; Here is the master function:
(defun translate nil
  (gp-translate-on-other-file)
  
  ;; Now starts the translation:
  (translate-with)
  )


;;---------------------
;; Translation of with
;;---------------------

(defvar translate-with-number 0
 "The next variable of a `with' function will be replaced by the
identifier whose name is the concatenation of \"with\" with this
number.")

(defun translate-with nil
  "Understand the syntax \"with(foo,to_do)\" in a gp-program, where foo
is an expression evaluating to a vector, as follows: any subsequent
dot `.' not preceded by a character of the set []a-zA-Z0-9_] is
replaced by this evaluation. An auxiliary variable with# is used where
# is an integer given by the variable 'translate-with-number.
Imbricated with are allowed and the innermost one has priority. "

  (goto-char (point-max))
  (while (re-search-backward "\\([^a-zA-Z_0-9]\\|\\`\\)with(" nil t)
         (goto-char (match-end 0))
         (let ((father (buffer-substring (point)
                                         (gp-looking-at-rat-exp)))
               (replacement
                 (concat "with" (number-to-string translate-with-number)))
               (p-end (save-excursion
                       (forward-char -1) (forward-sexp)
                       (- (point) 1))))
              (setq translate-with-number (+ 1 translate-with-number))
              ;; Erase the command:
              (forward-char -5)
              (delete-char (+ 6 (length father)))
              ;; Insert new variable:
              (insert (concat replacement "=" father ";\n"))
              (setq p-end (- p-end
                             (- (length replacement) 3)))
              ;; Erase last ):
              (save-excursion (goto-char p-end) (delete-char 1))
              ;; Replace proper `.' by new variable:
              (while (re-search-forward "[^]a-zA-Z0-9_]\\." (- p-end 1) t)
                     (forward-char -1) (delete-char 1)
                     (insert replacement)
                     (setq p-end (+ p-end (- (length replacement) 1)))
                     (forward-char 1))))
  ;; Set the counter back to 0 to avoid creating to many
  ;; variables:
  (setq translate-with-number 0))  


;; with-syntax.el ends here
