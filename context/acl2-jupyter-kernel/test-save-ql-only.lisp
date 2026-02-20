;;; Test: does save-exec with JUST quicklisp (no kernel system) break include-book?
;;;
;;; Usage:  /home/acl2/saved_acl2 < test-save-ql-only.lisp
;;; Then:   ./test-ql-only-image

;; Exit LP
(value :q)
(sb-ext:disable-debugger)

;; Load ONLY quicklisp (no ql:quickload)
(load "/home/jovyan/quicklisp/setup.lisp")
(format t "~%Quicklisp loaded. Saving...~%")

(save-exec "/workspaces/acl2-jupyter-stp/context/acl2-jupyter-kernel/test-ql-only-image" nil
           :init-forms '((set-raw-mode-on!)
                         (format t "~%=== include-book after QL-only save-exec ===~%")
                         (handler-case
                             (progn
                               (include-book "std/lists/append" :dir :system)
                               (cw "QL-ONLY: SUCCESS~%"))
                           (serious-condition (c)
                             (format t "QL-ONLY: SERIOUS: ~A~%" c)))
                         (value :q)))
