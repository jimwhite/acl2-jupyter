;;;; ACL2 Jupyter Kernel - Package Definitions

(defpackage #:acl2-jupyter-kernel
  (:nicknames #:jupyter/acl2)
  (:use #:common-lisp)
  (:export #:kernel
           #:start
           #:install
           #:install-image))
