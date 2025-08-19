(in-package #:jupyter/acl2)

(defclass kernel (jupyter/common-lisp:kernel)
  ((environment
     :reader kernel-environment
     :initform #+sbcl (sb-kernel:make-null-lexenv)
               #-sbcl nil))
  (:default-initargs
    :name "acl2"
    :package (find-package :common-lisp-user)
    :version "0.1"
    :banner "acl2-jupyter: an ACL2 Jupyter kernel
(C) 2025 Jim White <jim@fovi.com>"
    :language-name "common-lisp"
    :language-version (uiop:lisp-version-string)
    :mime-type "text/x-common-lisp"
    :file-extension ".lisp"
    :pygments-lexer "common-lisp"
    :codemirror-mode "text/x-common-lisp"
    :debugger t
    :help-links '(("ACL2 Documentation" . "https://www.cs.utexas.edu/~moore/acl2/acl2-doc.html")
                  ("ACL2 GitHub Repository" . "https://github.com/acl2/acl2")
                  ("ACL2-Jupyter GitHub Repository" . "https://github.com/jimwhite/acl2-jupyter")
                  ("Common Lisp Documentation" . "https://common-lisp.net/documentation")
                  ("Common Lisp HyperSpec" . "http://www.lispworks.com/documentation/HyperSpec/Front/index.htm")
                  ("Practical Common Lisp" . "http://www.gigamonkeys.com/book/")
                  ("The Common Lisp Cookbook" . "https://lispcookbook.github.io/cl-cookbook/")
                  #+sbcl ("SBCL Website" . "http://sbcl.org/"))))

(defmethod jupyter:evaluate-code ((kernel acl2-jupyter-kernel) code-string &rest args)
  ;; Parse the incoming code string as an ACL2 form (can be a list of forms)
  (let* ((form (read-from-string (concatenate 'string "(" code-string ")")))
         (out (make-string-output-stream)))
    ;; Evaluate as ACL2 logic
    (let ((ld-result (ld form
                         :ld-error-action :return
                         :ld-verbose nil
                         :ld-prompt nil
                         :ld-pre-eval-print nil
                         :standard-co out)))
      (get-output-stream-string out)))) ; Return output for Jupyter to display

