;;;; ACL2 Jupyter Kernel - Installer
;;;;
;;;; Installs the ACL2 Jupyter kernelspec so Jupyter can find and launch it.
;;;;
;;;; The kernel is launched by invoking the SBCL binary directly with
;;;; --core pointing at a pre-built .core file that has the kernel system
;;;; loaded. The connection file is passed via the JUPYTER_CONNECTION_FILE
;;;; environment variable (set in kernel.json "env").
;;;;
;;;; Two modes:
;;;;   1. Core mode (install):  Points kernel.json at sbcl + a .core file
;;;;      (created by build-kernel-image.sh via save-lisp-and-die).
;;;;   2. Image mode (install-image): Saves the current process as an
;;;;      executable image via uiop:dump-image.

(in-package #:acl2-jupyter-kernel)

;;; ---------------------------------------------------------------------------
;;; Constants
;;; ---------------------------------------------------------------------------

(defvar +display-name+ "ACL2")
(defvar +language+ "acl2")

;;; Default path to the .core file (sibling of this source file).
(defvar +default-core+
  (let ((here (or *load-pathname* *compile-file-pathname*)))
    (when here
      (namestring (merge-pathnames "acl2-jupyter-kernel.core" here)))))

;;; SBCL binary path — determined at load time from the running process.
(defvar +sbcl-program+
  (or (and (boundp 'sb-ext:*runtime-pathname*)
           (namestring (truename sb-ext:*runtime-pathname*)))
      "/usr/local/bin/sbcl"))

;;; SBCL_HOME for the generated script.
(defvar +sbcl-home+
  (or (uiop:getenv "SBCL_HOME") "/usr/local/lib/sbcl/"))

;;; Dynamic space size (MB) — inherit from current ACL2 build.
(defvar +dynamic-space-size+
  (let ((sym (find-symbol "*SBCL-DYNAMIC-SPACE-SIZE*" "ACL2")))
    (if (and sym (boundp sym))
        (format nil "~A" (symbol-value sym))
        "32000")))

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
;;; kernel.json argv launches sbcl directly with the right runtime options,
;;; --core pointing at the pre-built .core file, and --eval to initialize
;;; ACL2 and start the kernel. The connection file is passed via the
;;; JUPYTER_CONNECTION_FILE environment variable (in kernel.json env).

(defun make-sbcl-argv (core-path)
  "Build the argv list for launching sbcl with the kernel core.
   The {connection_file} placeholder goes last, just like the CL SBCL kernel.
   run-kernel picks it up via (first (uiop:command-line-arguments))."
  (list +sbcl-program+
        "--tls-limit" "16384"
        "--dynamic-space-size" +dynamic-space-size+
        "--control-stack-size" "64"
        "--disable-ldb"
        "--core" core-path
        "--end-runtime-options"
        "--no-userinit"
        "--eval" "(acl2::sbcl-restart)"
        "--eval" "(acl2-jupyter-kernel:start)"
        "{connection_file}"))

(defmethod jupyter:command-line ((instance acl2-user-installer))
  "Get the command line for a user installation."
  (let ((core (or (jupyter:installer-implementation instance)
                  +default-core+
                  (error "Cannot determine path to .core file."))))
    (make-sbcl-argv core)))

(defmethod jupyter:command-line ((instance acl2-system-installer))
  "Get the command line for a system installation."
  (let ((core (or (jupyter:installer-implementation instance)
                  +default-core+
                  (error "Cannot determine path to .core file."))))
    (make-sbcl-argv core)))

;;; ---------------------------------------------------------------------------
;;; Kernel Spec Override
;;; ---------------------------------------------------------------------------
;;; Override install-spec to add the "env" dict to kernel.json.
;;; Jupyter supports env vars in the kernel spec — we use it to pass
;;; SBCL_HOME and the connection file path.

(defun install-acl2-spec (instance)
  "Install kernel.json with env dict for SBCL_HOME and connection file."
  (let ((spec-path (jupyter:installer-path instance :spec)))
    (format t "Installing kernel spec file ~A~%" spec-path)
    (with-open-file (stream spec-path :direction :output :if-exists :supersede)
      (shasht:write-json
        (list :object-plist
          "argv" (jupyter:command-line instance)
          "display_name" (jupyter:installer-display-name instance)
          "language" (jupyter:installer-language instance)
          "interrupt_mode" "message"
          "env" (list :object-plist
                  "SBCL_HOME" +sbcl-home+)
          "metadata" :empty-object)
        stream))))


;;; ---------------------------------------------------------------------------
;;; Public Install Functions
;;; ---------------------------------------------------------------------------

(defun install (&key core system local prefix jupyter program)
  "Install the ACL2 Jupyter kernel.
   - CORE: path to the .core file (default: sibling of this source file)
   - SYSTEM: if T, install system-wide; otherwise install for current user
   - LOCAL: use /usr/local/share instead of /usr/share for system installs
   - PREFIX: directory prefix for packaging
   - JUPYTER: Jupyter directory override
   - PROGRAM: program directory override"
  (let ((instance (make-instance
                    (if system 'acl2-system-installer 'acl2-user-installer)
                    :display-name +display-name+
                    :implementation (or core +default-core+)
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
