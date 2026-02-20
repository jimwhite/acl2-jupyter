;;;; ACL2 Jupyter Kernel - Code Inspection
;;;;
;;;; Provides ACL2-aware documentation lookup for shift-tab inspection
;;;; in the Jupyter frontend.

(in-package #:acl2-jupyter-kernel)

(defun get-acl2-doc (sym)
  "Get the ACL2 documentation string for SYM, if available."
  (ignore-errors
    (let ((state acl2::*the-live-state*))
      (declare (ignorable state))
      ;; Try to get the :doc string from ACL2's documentation database
      (let ((doc-pair (assoc sym (acl2::global-val 'acl2::documentation-alist
                                                    (acl2::w state)))))
        (when doc-pair
          (cdr doc-pair))))))

(defun get-function-doc (sym)
  "Get the CL documentation string for SYM as a function."
  (ignore-errors (documentation sym 'function)))

(defun get-variable-doc (sym)
  "Get the CL documentation string for SYM as a variable."
  (ignore-errors (documentation sym 'variable)))

(defun get-function-arglist (sym)
  "Get the arglist for function SYM."
  (ignore-errors
    (cond
      ((macro-function sym)
       ;; For macros, try to get formals from ACL2 world
       (let ((formals (ignore-errors
                        (acl2::getpropc sym 'acl2::macro-args nil
                                        (acl2::w acl2::*the-live-state*)))))
         (or formals
             #+sbcl (sb-introspect:function-lambda-list (macro-function sym))
             #-sbcl nil)))
      ((fboundp sym)
       ;; For functions, try ACL2 formals first, then CL introspection
       (let ((formals (ignore-errors
                        (acl2::getpropc sym 'acl2::formals nil
                                        (acl2::w acl2::*the-live-state*)))))
         (or formals
             #+sbcl (sb-introspect:function-lambda-list (fdefinition sym))
             #-sbcl nil))))))

(defun get-symbol-properties (sym)
  "Get a summary of ACL2 world properties for SYM."
  (ignore-errors
    (let* ((world (acl2::w acl2::*the-live-state*))
           (props nil))
      ;; Check if it's a defun
      (when (acl2::getpropc sym 'acl2::formals :none world)
        (push "Function" props))
      ;; Check if it's a macro
      (when (acl2::getpropc sym 'acl2::macro-args nil world)
        (push "Macro" props))
      ;; Check if it's a theorem
      (when (acl2::getpropc sym 'acl2::theorem nil world)
        (push "Theorem" props))
      ;; Check if it's defconst
      (when (acl2::getpropc sym 'acl2::const nil world)
        (push "Constant" props))
      ;; Check if it has a stobj definition
      (when (acl2::getpropc sym 'acl2::stobj nil world)
        (push "Stobj" props))
      props)))

(defmethod jupyter:inspect-code ((k kernel) code cursor-pos detail-level)
  "Inspect ACL2 symbol at cursor position."
  (declare (ignore detail-level))
  (let* ((*package* (find-package "ACL2"))
         (start (find-token-start code cursor-pos))
         (end cursor-pos)
         ;; Extend end to cover the full symbol
         (end (loop for i from end below (length code)
                    for ch = (char code i)
                    while (and (not (member ch '(#\Space #\Tab #\Newline #\Return
                                                  #\( #\) #\' #\` #\, #\" #\;)))
                               (graphic-char-p ch))
                    finally (return i)))
         (token (string-upcase (subseq code start end)))
         (sym (find-symbol token "ACL2")))
    (unless sym
      ;; Try COMMON-LISP package
      (setf sym (find-symbol token "COMMON-LISP")))
    (if sym
        (let ((parts nil))
          ;; Header
          (let ((*print-case* :downcase))
            (push (format nil "### ~A" (symbol-name sym)) parts))

          ;; Type info from ACL2 world
          (let ((properties (get-symbol-properties sym)))
            (when properties
              (push (format nil "**Type:** ~{~A~^, ~}" properties) parts)))

          ;; Arglist
          (let ((arglist (get-function-arglist sym)))
            (when arglist
              (let ((*print-case* :downcase))
                (push (format nil "**Signature:** `(~A~{ ~A~})`"
                              (symbol-name sym)
                              (mapcar #'prin1-to-string arglist))
                      parts))))

          ;; Guard (for ACL2 functions)
          (ignore-errors
            (let ((guard (acl2::getpropc sym 'acl2::guard nil
                                         (acl2::w acl2::*the-live-state*))))
              (when guard
                (let ((*print-case* :downcase)
                      (*print-pretty* t))
                  (push (format nil "**Guard:** `~A`" (prin1-to-string guard))
                        parts)))))

          ;; Documentation
          (let ((doc (or (get-acl2-doc sym)
                         (get-function-doc sym)
                         (get-variable-doc sym))))
            (when doc
              (push (format nil "~%~A" doc) parts)))

          ;; Current value for bound variables/constants
          (when (boundp sym)
            (let ((*print-case* :downcase)
                  (*print-pretty* t)
                  (*print-length* 10)
                  (*print-level* 3))
              (push (format nil "**Value:** `~A`" (prin1-to-string (symbol-value sym)))
                    parts)))

          (jupyter:markdown (format nil "~{~A~^~%~%~}" (nreverse parts))))
        (jupyter:text "No documentation found."))))
