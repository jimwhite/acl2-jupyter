;;;; ACL2 Jupyter Kernel - Installer
;;;;
;;;; Installs the ACL2 Jupyter kernelspec so Jupyter can find and launch it.
;;;;
;;;; kernel.json argv calls the Lisp implementation directly with the
;;;; saved_acl2 core/image, loads Quicklisp and the kernel system via
;;;; --eval, then starts the kernel.  No shell script wrapper.
;;;;
;;;; Implementation-specific argv construction is dispatched via
;;;; UIOP:IMPLEMENTATION-TYPE.

(in-package #:acl2-jupyter)

;;; ---------------------------------------------------------------------------
;;; Constants
;;; ---------------------------------------------------------------------------

(defvar +display-name+ "ACL2")
(defvar +language+ "acl2")

;;; ---------------------------------------------------------------------------
;;; Path Discovery  (implementation-neutral, uses UIOP)
;;; ---------------------------------------------------------------------------

(defun find-lisp-runtime ()
  "Return the absolute path to the current Lisp implementation's executable."
  (let ((impl (string-downcase (symbol-name (uiop:implementation-type)))))
    (string-right-trim
     '(#\Newline #\Space #\Return)
     (uiop:run-program (list "which" impl) :output :string))))

(defun find-acl2-core ()
  "Return the path to the ACL2 core/image file."
  (let* ((acl2-home (uiop:ensure-directory-pathname
                     (or (uiop:getenv "ACL2_HOME") "/home/acl2")))
         (core (merge-pathnames "saved_acl2.core" acl2-home)))
    (unless (probe-file core)
      (error "Cannot find ACL2 core at ~A" core))
    (namestring core)))

(defun find-quicklisp-setup ()
  "Return the path to quicklisp/setup.lisp."
  (let ((setup (merge-pathnames "quicklisp/setup.lisp"
                                (uiop:ensure-directory-pathname
                                 (user-homedir-pathname)))))
    (unless (probe-file setup)
      (error "Cannot find quicklisp setup at ~A" setup))
    (namestring setup)))

;;; ---------------------------------------------------------------------------
;;; Installer Classes
;;; ---------------------------------------------------------------------------

(defclass acl2-installer (jupyter:installer)
  ((lisp-runtime :initarg :lisp-runtime :accessor installer-lisp-runtime)
   (core-path :initarg :core-path :accessor installer-core-path)
   (quicklisp-setup :initarg :quicklisp-setup :accessor installer-quicklisp-setup))
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
;;; Command Line Generation  (implementation-dispatched)
;;; ---------------------------------------------------------------------------

(defgeneric make-kernel-argv (impl lisp-runtime core-path quicklisp-setup)
  (:documentation "Build the argv list for kernel.json, dispatched on IMPL
   (a keyword like :SBCL or :CCL)."))

(defmethod make-kernel-argv ((impl (eql :sbcl)) lisp-runtime core-path
                             quicklisp-setup)
  (list lisp-runtime
        "--tls-limit" "16384"
        "--dynamic-space-size" "32000"
        "--control-stack-size" "64"
        "--disable-ldb"
        "--core" core-path
        "--end-runtime-options"
        "--no-userinit"
        "--load" quicklisp-setup
        "--eval" "(ql:quickload :acl2-jupyter-kernel :silent t)"
        "--eval" "(acl2-jupyter-kernel:start \"{connection_file}\")"))

(defmethod jupyter:command-line ((instance acl2-installer))
  "Get the command line for an ACL2 kernel installation."
  (make-kernel-argv (uiop:implementation-type)
                    (installer-lisp-runtime instance)
                    (installer-core-path instance)
                    (installer-quicklisp-setup instance)))

;;; ---------------------------------------------------------------------------
;;; Environment Variables  (implementation-dispatched)
;;; ---------------------------------------------------------------------------

(defgeneric make-kernel-env (impl)
  (:documentation "Return a plist of environment variables for kernel.json,
   dispatched on IMPL (a keyword like :SBCL or :CCL)."))

(defmethod make-kernel-env ((impl (eql :sbcl)))
  (let ((sbcl-home (or (uiop:getenv "SBCL_HOME") "/usr/local/lib/sbcl/")))
    (list :object-plist "SBCL_HOME" sbcl-home)))

;;; ---------------------------------------------------------------------------
;;; Kernel Spec Override
;;; ---------------------------------------------------------------------------

(defun install-acl2-spec (instance)
  "Install kernel.json for the ACL2 kernel."
  (let ((spec-path (jupyter:installer-path instance :spec)))
    (format t "Installing kernel spec file ~A~%" spec-path)
    (with-open-file (stream spec-path :direction :output :if-exists :supersede)
      (shasht:write-json
        (list :object-plist
          "argv" (jupyter:command-line instance)
          "display_name" (jupyter:installer-display-name instance)
          "language" (jupyter:installer-language instance)
          "interrupt_mode" "message"
          "metadata" :empty-object
          "env" (make-kernel-env (uiop:implementation-type)))
        stream))))


;;; ---------------------------------------------------------------------------
;;; Public Install Functions
;;; ---------------------------------------------------------------------------

(defun install (&key system local prefix jupyter program
                     lisp-runtime core-path quicklisp-setup)
  "Install the ACL2 Jupyter kernel.
   Paths are auto-detected from the running environment unless overridden.
   - SYSTEM: if T, install system-wide; otherwise install for current user
   - LOCAL: use /usr/local/share instead of /usr/share for system installs
   - PREFIX: directory prefix for packaging
   - JUPYTER: Jupyter directory override
   - PROGRAM: program directory override
   - LISP-RUNTIME: path to Lisp executable (auto-detected)
   - CORE-PATH: path to saved_acl2.core (auto-detected)
   - QUICKLISP-SETUP: path to quicklisp/setup.lisp (auto-detected)"
  (let ((instance (make-instance
                    (if system 'acl2-system-installer 'acl2-user-installer)
                    :display-name +display-name+
                    :kernel-name +language+
                    :lisp-runtime (or lisp-runtime (find-lisp-runtime))
                    :core-path (or core-path (find-acl2-core))
                    :quicklisp-setup (or quicklisp-setup (find-quicklisp-setup))
                    :local local
                    :prefix prefix
                    :jupyter-path jupyter
                    :program-path program)))
    (jupyter::install-directories instance)
    (install-acl2-spec instance)
    (jupyter::install-resources instance)
    (jupyter::install-local-systems instance)))

(defun install-image (&key prefix jupyter program)
  "Install the ACL2 kernel based on a saved image of the current process."
  (jupyter:install
    (make-instance 'acl2-user-image-installer
      :display-name +display-name+
      :kernel-name +language+
      :prefix prefix
      :jupyter-path jupyter
      :program-path program)))
