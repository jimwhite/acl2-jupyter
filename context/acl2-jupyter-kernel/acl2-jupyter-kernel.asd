;;;; ACL2 Jupyter Kernel - ASDF System Definition
;;;;
;;;; A Jupyter kernel for the ACL2 theorem prover, built on common-lisp-jupyter.
;;;; This kernel runs inside ACL2 (saved_acl2) and evaluates ACL2 forms directly,
;;;; with proper STATE binding, output routing for CW/FMT, and ACL2-aware
;;;; code completion and inspection.

(asdf:defsystem "acl2-jupyter-kernel"
  :description "A Jupyter kernel for the ACL2 theorem prover."
  :author "ACL2 Jupyter Contributors"
  :license "MIT"
  :version "0.1.0"
  :depends-on ("common-lisp-jupyter" "bt-semaphore" "bordeaux-threads")
  :serial t
  :components
    ((:file "packages")
     (:file "kernel")
     (:file "complete")
     (:file "inspect")
     (:file "installer")))
