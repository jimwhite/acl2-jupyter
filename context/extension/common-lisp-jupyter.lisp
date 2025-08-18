; (depends-on "common-lisp-jupyter-raw.lsp")
(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)

;(defttag :quicklisp)
(include-book "quicklisp/cl-fad" :dir :system :ttags :all)

(defttag :common-lisp-jupyter)
(include-raw "common-lisp-jupyter-raw.lsp" :do-not-compile t)
