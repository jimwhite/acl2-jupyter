;;;; ACL2 Jupyter Kernel - Kernel Class
;;;;
;;;; Subclasses jupyter:kernel to provide ACL2-specific evaluation.
;;;; ACL2 forms are evaluated with STATE bound to *the-live-state*,
;;;; and output from CW, FMT, etc. is routed through Jupyter's streams.

(in-package #:acl2-jupyter-kernel)

;;; ---------------------------------------------------------------------------
;;; ACL2 Output Routing
;;; ---------------------------------------------------------------------------
;;; The bridge uses a custom gray stream class and macros to redirect ACL2's
;;; output channels (standard-co, proofs-co, trace-co) to a given stream.
;;; We reuse the same pattern here to route output through Jupyter's streams.

(defmacro with-acl2-channels-bound (channel &body forms)
  "Bind ACL2's output channels (proofs-co, standard-co, trace-co) to CHANNEL."
  `(progv
       (list (acl2::global-symbol 'acl2::proofs-co)
             (acl2::global-symbol 'acl2::standard-co)
             (acl2::global-symbol 'acl2::trace-co))
       (list ,channel ,channel ,channel)
     (progn ,@forms)))

(defmacro with-acl2-output-to (stream &body forms)
  "Redirect all ACL2 output (standard-co, proofs-co, trace-co, *standard-output*,
   *trace-output*, *error-output*) to STREAM, then execute FORMS."
  (let ((channel (gensym "CHANNEL")))
    `(let* ((,channel (gensym "ACL2-JUPYTER-OUT")))
       (setf (get ,channel acl2::*open-output-channel-type-key*) :character)
       (setf (get ,channel acl2::*open-output-channel-key*) ,stream)
       (unwind-protect
           (let ((*standard-output* ,stream)
                 (*trace-output*    ,stream)
                 (*debug-io*        ,stream)
                 (*error-output*    ,stream)
                 (acl2::*standard-co* ,channel))
             (with-acl2-channels-bound ,channel ,@forms))
         ;; Clean up the symbol properties so GC can reclaim the stream.
         (setf (get ,channel acl2::*open-output-channel-key*) nil)
         (setf (get ,channel acl2::*open-output-channel-type-key*) nil)))))

;;; ---------------------------------------------------------------------------
;;; REPL Variables
;;; ---------------------------------------------------------------------------
;;; Emulate the standard CL REPL variables (-, +, ++, +++, *, **, ***, /, //, ///)
;;; within the ACL2 package context.

(defvar *acl2-last-form* nil
  "The last form read (ACL2's equivalent of CL:-)")
(defvar *acl2-results* nil
  "The last set of result values (CL's /)")

;;; ---------------------------------------------------------------------------
;;; Kernel Class
;;; ---------------------------------------------------------------------------

(defclass kernel (jupyter:kernel)
  ()
  (:default-initargs
    :name "acl2"
    :package (find-package "ACL2")
    :version "0.1.0"
    :banner (format nil "ACL2 Jupyter Kernel v0.1.0~%~A"
                    (acl2::f-get-global 'acl2::acl2-version
                                        acl2::*the-live-state*))
    :language-name "acl2"
    :language-version (acl2::f-get-global 'acl2::acl2-version
                                          acl2::*the-live-state*)
    :mime-type "text/x-common-lisp"
    :file-extension ".lisp"
    :pygments-lexer "common-lisp"
    :codemirror-mode "text/x-common-lisp"
    :help-links '(("ACL2 Documentation" . "https://www.cs.utexas.edu/~moore/acl2/")
                  ("ACL2 Manual" . "https://www.cs.utexas.edu/~moore/acl2/current/manual/")
                  ("ACL2 Community Books" . "https://www.cs.utexas.edu/~moore/acl2/current/combined-manual/"))))


;;; ---------------------------------------------------------------------------
;;; ACL2 Form Evaluation
;;; ---------------------------------------------------------------------------

(defun acl2-eval (form)
  "Evaluate a single ACL2 form with STATE bound to *the-live-state*.
   Returns a list of result values."
  (multiple-value-list
   (eval
    ;; Bind STATE so that ACL2 macros and functions that use it work directly.
    ;; This is the same pattern used by the ACL2 Bridge.
    `(let ((acl2::state acl2::*the-live-state*))
       (declare (ignorable acl2::state))
       ,form))))

(defun read-acl2-forms (code)
  "Read all forms from a string of ACL2 code.
   Returns a list of forms. Handles ACL2 keyword commands (e.g. :pe, :pl)
   as well as standard s-expressions."
  (let ((forms nil)
        (*package* (find-package "ACL2"))
        (*readtable* (copy-readtable nil)))
    (with-input-from-string (stream code)
      (loop
        ;; Skip whitespace
        (loop for ch = (peek-char nil stream nil nil)
              while (and ch (member ch '(#\Space #\Tab #\Newline #\Return)))
              do (read-char stream))
        ;; Check for EOF
        (let ((ch (peek-char nil stream nil nil)))
          (when (null ch) (return))
          ;; Check for ACL2 keyword commands (lines starting with :)
          (cond
            ((char= ch #\:)
             ;; Read the whole line as a keyword command
             (let ((line (string-trim '(#\Space #\Tab #\Return)
                                      (read-line stream nil ""))))
               (when (plusp (length line))
                 ;; Parse it: read symbols from the line
                 (let ((cmd-forms nil))
                   (with-input-from-string (ls line)
                     (handler-case
                         (loop for obj = (read ls nil ls)
                               until (eq obj ls)
                               do (push obj cmd-forms))
                       (error () nil)))
                   (when cmd-forms
                     (push (nreverse cmd-forms) forms))))))
            ;; Check for comment lines
            ((char= ch #\;)
             (read-line stream nil ""))
            (t
             ;; Standard s-expression
             (handler-case
                 (let ((form (read stream nil stream)))
                   (unless (eq form stream)
                     (push form forms)))
               (error (c)
                 ;; If there's a read error, capture the rest as a string
                 ;; and report it later during evaluation
                 (let ((rest (read-line stream nil "")))
                   (push `(acl2::er acl2::soft 'acl2-jupyter-kernel
                                    "Read error: ~@0 near: ~@1"
                                    ,(format nil "~A" c)
                                    ,rest)
                         forms)))))))))
    (nreverse forms)))

(defmethod jupyter:evaluate-code ((k kernel) code &optional source-path breakpoints)
  "Evaluate ACL2 code in the kernel.
   Each top-level form is evaluated sequentially. Results are displayed
   via execute-result. Errors are caught and reported."
  (declare (ignore source-path breakpoints))
  (let* ((*package* (find-package "ACL2"))
         (forms (read-acl2-forms code))
         (acl2::state acl2::*the-live-state*))
    (declare (ignorable acl2::state))
    (dolist (form forms)
      (setf *acl2-last-form* form)
      (with-acl2-output-to *standard-output*
        (handler-case
            (let ((results (acl2-eval form)))
              (setf *acl2-results* results)
              ;; Display each result value
              (dolist (result results)
                ;; Don't display STATE (it's not informative)
                (unless (eq result acl2::*the-live-state*)
                  (jupyter:execute-result
                   (jupyter:text
                    (let ((*package* (find-package "ACL2"))
                          (*print-case* :downcase)
                          (*print-pretty* t))
                      (prin1-to-string result)))))))
          (error (c)
            (return-from jupyter:evaluate-code
              (values (symbol-name (type-of c))
                      (format nil "~A" c)
                      (list (format nil "~A" c))))))))))

(defmethod jupyter:code-is-complete ((k kernel) code)
  "Check if ACL2 code is complete (balanced parens, etc.)."
  (let ((*package* (find-package "ACL2")))
    (handler-case
        (progn
          (read-acl2-forms code)
          "complete")
      (end-of-file () "incomplete")
      (error () "invalid"))))
