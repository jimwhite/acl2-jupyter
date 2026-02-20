;;; Test save-exec + restore cycle with quicklisp.
;;; This saves a minimal image with quicklisp loaded and tests include-book
;;; after restore.
;;;
;;; Usage:  /home/acl2/saved_acl2 < test-save-restore.lisp
;;; Then:   ./test-saved-image < test-include-book-original.lisp

;; Exit LP to raw Lisp
(value :q)
(sb-ext:disable-debugger)

;; Load quicklisp + our kernel system (same as build-kernel-image.sh)
(load "/home/jovyan/quicklisp/setup.lisp")
(ql:quickload :acl2-jupyter-kernel :silent t)
(format t "~%Loaded. Saving image...~%")

;; Save with init-forms (same as our build script)
(save-exec "/workspaces/acl2-jupyter-stp/context/acl2-jupyter-kernel/test-saved-image" nil
           :init-forms '((set-raw-mode-on!)
                         (format t "~%=== Testing include-book after save-exec restore ===~%")
                         (handler-case
                             (progn
                               (include-book "std/lists/append" :dir :system)
                               (cw "SAVE-RESTORE-INCLUDE-BOOK: SUCCESS~%"))
                           (error (c)
                             (format t "SAVE-RESTORE-INCLUDE-BOOK: ERROR: ~A~%" c))
                           (serious-condition (c)
                             (format t "SAVE-RESTORE-INCLUDE-BOOK: SERIOUS: ~A~%" c)))
                         (value :q)))
