(defpackage #:jupyter/acl2
  (:use #:common-lisp)
  (:documentation "Provides ACL2 kernel support.")
  (:export #:debug-environment
	         #:install
	         #:install-image
	         #:install-roswell
	         #:kernel))

(in-package #:jupyter/acl2)

#+sbcl (require :sb-introspect)
