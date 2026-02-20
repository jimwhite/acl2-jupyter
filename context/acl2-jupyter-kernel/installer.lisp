;;;; ACL2 Jupyter Kernel - Installer
;;;;
;;;; Installs the ACL2 Jupyter kernelspec so Jupyter can find and launch it.
;;;;
;;;; The kernel is launched by start-kernel.sh, which invokes SBCL directly
;;;; with the original saved_acl2.core (no save-exec, no second core image).
;;;; Quicklisp and the kernel system are loaded at startup via --eval,
;;;; then sbcl-restart enters LP, which reads (set-raw-mode-on!) and
;;;; (acl2-jupyter-kernel:start) from stdin.
;;;;
;;;; kernel.json argv is:
;;;;   ["path/to/start-kernel.sh", "{connection_file}"]

(in-package #:acl2-jupyter)

;;; ---------------------------------------------------------------------------
;;; Constants
;;; ---------------------------------------------------------------------------

(defvar +display-name+ "ACL2")
(defvar +language+ "acl2")

;;; Default path to the launcher script (sibling of this source file).
(defvar +default-binary+
  (let ((here (or *load-pathname* *compile-file-pathname*)))
    (when here
      (namestring (merge-pathnames "start-kernel.sh" here)))))

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
;;; kernel.json argv invokes start-kernel.sh with {connection_file}.
;;; The script loads the kernel into the original saved_acl2 at startup.

(defun make-kernel-argv (binary-path)
  "Build the argv list for kernel.json.
   start-kernel.sh takes {connection_file} as its sole argument."
  (list binary-path "{connection_file}"))

(defmethod jupyter:command-line ((instance acl2-user-installer))
  "Get the command line for a user installation."
  (let ((binary (or (jupyter:installer-implementation instance)
                    +default-binary+
                    (error "Cannot determine path to saved binary."))))
    (make-kernel-argv binary)))

(defmethod jupyter:command-line ((instance acl2-system-installer))
  "Get the command line for a system installation."
  (let ((binary (or (jupyter:installer-implementation instance)
                    +default-binary+
                    (error "Cannot determine path to saved binary."))))
    (make-kernel-argv binary)))

;;; ---------------------------------------------------------------------------
;;; Kernel Spec Override
;;; ---------------------------------------------------------------------------
;;; Override install-spec to write kernel.json directly (the saved binary
;;; script already exports SBCL_HOME, so no env dict is needed).

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
          "metadata" :empty-object)
        stream))))


;;; ---------------------------------------------------------------------------
;;; Public Install Functions
;;; ---------------------------------------------------------------------------

(defun install (&key binary system local prefix jupyter program)
  "Install the ACL2 Jupyter kernel.
   - BINARY: path to the saved binary (default: sibling of this source file)
   - SYSTEM: if T, install system-wide; otherwise install for current user
   - LOCAL: use /usr/local/share instead of /usr/share for system installs
   - PREFIX: directory prefix for packaging
   - JUPYTER: Jupyter directory override
   - PROGRAM: program directory override"
  (let ((instance (make-instance
                    (if system 'acl2-system-installer 'acl2-user-installer)
                    :display-name +display-name+
                    :implementation (or binary +default-binary+)
                    :kernel-name +language+
                    :local local
                    :prefix prefix
                    :jupyter-path jupyter
                    :program-path program)))
    ;; Create directories and install resources using the parent method,
    ;; but write our own kernel.json with env support.
    (jupyter::install-directories instance)
    (install-acl2-spec instance)
    (jupyter::install-resources instance)
    ;; Call the specific install method for user/system (copies local systems etc.)
    (if system
        (jupyter::install-local-systems instance)
        (jupyter::install-local-systems instance))))

(defun install-image (&key prefix jupyter program)
  "Install the ACL2 kernel based on a saved image of the current process.
   This creates a standalone binary that includes all dependencies.
   The entry point calls acl2-jupyter-kernel:start which initializes
   ACL2 and then enters the Jupyter kernel event loop."
  (jupyter:install
    (make-instance 'acl2-user-image-installer
      :display-name +display-name+
      :kernel-name +language+
      :prefix prefix
      :jupyter-path jupyter
      :program-path program)))
