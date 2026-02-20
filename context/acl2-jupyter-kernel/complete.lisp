;;;; ACL2 Jupyter Kernel - Code Completion
;;;;
;;;; Provides ACL2-aware symbol completion for the Jupyter frontend.
;;;; Completes function names, macro names, theorem names, and other
;;;; ACL2 symbols.

(in-package #:acl2-jupyter)

(defun symbol-type-string (sym)
  "Return a string describing what kind of ACL2 entity SYM is."
  (cond
    ((macro-function sym) "macro")
    ((fboundp sym) "function")
    ((boundp sym) "variable")
    (t "symbol")))

(defun find-token-start (code cursor-pos)
  "Find the start position of the token at CURSOR-POS in CODE.
   A token is a sequence of characters that can appear in a Lisp symbol."
  (let ((start cursor-pos))
    (loop while (and (> start 0)
                     (let ((ch (char code (1- start))))
                       (and (not (member ch '(#\Space #\Tab #\Newline #\Return
                                              #\( #\) #\' #\` #\, #\" #\;)))
                            (graphic-char-p ch))))
          do (decf start))
    start))

(defmethod jupyter:complete-code ((k kernel) match-set code cursor-pos)
  "Complete ACL2 symbols at the cursor position."
  (let* ((*package* (find-package "ACL2"))
         (start (find-token-start code cursor-pos))
         (prefix (string-upcase (subseq code start cursor-pos)))
         (prefix-len (length prefix)))
    (when (plusp prefix-len)
      ;; Search for matching symbols in the ACL2 package and imported packages
      (dolist (pkg (list (find-package "ACL2")
                         (find-package "ACL2-INPUT-CHANNEL")
                         (find-package "ACL2-OUTPUT-CHANNEL")
                         (find-package "COMMON-LISP")))
        (when pkg
          (do-external-symbols (sym pkg)
            (let ((name (symbol-name sym)))
              (when (and (>= (length name) prefix-len)
                         (string= prefix name :end2 prefix-len))
                (let ((display-name (let ((*print-case* :downcase))
                                      (symbol-name sym))))
                  (jupyter:match-set-add match-set
                                         display-name
                                         start cursor-pos
                                         :type (symbol-type-string sym)))))))))))
