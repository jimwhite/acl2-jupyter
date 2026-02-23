;;; capture-boot-metadata-loader.lisp — Bootstrap loader
;;;
;;; Loads init.lisp to create the ACL2 package, then loads the main
;;; capture script which uses acl2:: prefixed symbols.
;;;
;;; Usage:
;;;   cd /home/acl2
;;;   sbcl --dynamic-space-size 32000 --control-stack-size 64 \
;;;        --disable-ldb --disable-debugger --no-userinit \
;;;        --load /path/to/capture-boot-metadata-loader.lisp

(in-package "COMMON-LISP-USER")

#+sbcl (sb-ext:disable-debugger)

(handler-case
    (progn
      (format t "~&;; Loading init.lisp to create ACL2 package ...~%")
      (load "init.lisp")
      (format t "~&;; ACL2 package ready. Loading capture script ...~%")
      ;; Resolve path relative to this loader file.
      (let ((capture-script
              (merge-pathnames "capture-boot-metadata.lisp"
                               *load-pathname*)))
        (load capture-script)))
  (serious-condition (c)
    (format *error-output* "~&;; FATAL ERROR: ~A~%" c)
    #+sbcl (sb-ext:exit :code 1)
    #-sbcl (quit 1)))
