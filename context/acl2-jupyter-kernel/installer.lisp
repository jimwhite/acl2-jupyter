;;;; ACL2 Jupyter Kernel - Installer
;;;;
;;;; Installs the ACL2 Jupyter kernelspec so Jupyter can find and launch it.
;;;; The kernel is launched using the ACL2 binary (saved_acl2), which is SBCL
;;;; with ACL2 pre-loaded. On startup it loads quicklisp and common-lisp-jupyter
;;;; then runs the ACL2 kernel.

(in-package #:acl2-jupyter-kernel)

;;; ---------------------------------------------------------------------------
;;; Constants
;;; ---------------------------------------------------------------------------

(defvar +display-name+ "ACL2")
(defvar +language+ "acl2")

;;; The --eval flag for the Lisp implementation
(defvar +eval-flag+
  #+sbcl "--eval"
  #+ccl "--eval"
  #-(or sbcl ccl) "--eval")

;;; ---------------------------------------------------------------------------
;;; Installer Classes
;;; ---------------------------------------------------------------------------

(defclass acl2-installer (jupyter:installer)
  ()
  (:default-initargs
    :class 'kernel
    :language +language+
    :debugger nil
    :resources nil
    :systems '(:acl2-jupyter-kernel)))


(defclass acl2-system-installer (jupyter:system-installer acl2-installer)
  ()
  (:documentation "ACL2 Jupyter kernel system installer."))


(defclass acl2-user-installer (jupyter:user-installer acl2-installer)
  ()
  (:documentation "ACL2 Jupyter kernel user installer."))


(defclass acl2-user-image-installer (jupyter:user-image-installer acl2-installer)
  ()
  (:documentation "ACL2 Jupyter kernel user image installer."))


;;; ---------------------------------------------------------------------------
;;; Command Line Generation
;;; ---------------------------------------------------------------------------
;;; The kernel.json argv tells Jupyter how to launch the kernel process.
;;; We launch saved_acl2 (the ACL2 binary), then use --eval to load
;;; quicklisp, our kernel system, and start the kernel.

(defmethod jupyter:command-line ((instance acl2-user-installer))
  "Get the command line for a user installation."
  (let ((implementation (or (jupyter:installer-implementation instance)
                            ;; Default to the ACL2 binary
                            (or (uiop:getenv "ACL2")
                                "saved_acl2"))))
    (list implementation
          +eval-flag+
          (format nil "(progn ~
                         (require :sb-bsd-sockets) ~
                         (let ((ql-setup (merge-pathnames ~
                                  #P\"quicklisp/setup.lisp\" ~
                                  (user-homedir-pathname)))) ~
                           (when (probe-file ql-setup) (load ql-setup))) ~
                         (ql:quickload :acl2-jupyter-kernel) ~
                         (jupyter:run-kernel 'acl2-jupyter-kernel:kernel))")
          "{connection_file}")))


(defmethod jupyter:command-line ((instance acl2-system-installer))
  "Get the command line for a system installation."
  (jupyter:command-line
   (change-class (make-instance 'acl2-user-installer
                   :display-name (jupyter:installer-display-name instance)
                   :implementation (jupyter:installer-implementation instance)
                   :kernel-name (jupyter:installer-kernel-name instance))
                 'acl2-user-installer)))


;;; ---------------------------------------------------------------------------
;;; Public Install Functions
;;; ---------------------------------------------------------------------------

(defun install (&key bin-path system local prefix jupyter program)
  "Install the ACL2 Jupyter kernel.
   - BIN-PATH: path to the ACL2 binary (default: $ACL2 or 'saved_acl2')
   - SYSTEM: if T, install system-wide; otherwise install for current user
   - LOCAL: use /usr/local/share instead of /usr/share for system installs
   - PREFIX: directory prefix for packaging
   - JUPYTER: Jupyter directory override
   - PROGRAM: program directory override"
  (jupyter:install
    (make-instance
      (if system 'acl2-system-installer 'acl2-user-installer)
      :display-name +display-name+
      :implementation (or bin-path
                          (uiop:getenv "ACL2")
                          "saved_acl2")
      :kernel-name +language+
      :local local
      :prefix prefix
      :jupyter-path jupyter
      :program-path program)))

(defun install-image (&key prefix jupyter program)
  "Install the ACL2 kernel based on a saved image of the current process.
   This creates a standalone binary that includes all dependencies."
  (jupyter:install
    (make-instance 'acl2-user-image-installer
      :display-name +display-name+
      :kernel-name +language+
      :prefix prefix
      :jupyter-path jupyter
      :program-path program)))
