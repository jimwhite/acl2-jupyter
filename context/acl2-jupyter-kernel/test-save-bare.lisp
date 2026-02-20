;;; Test: does save-exec ALONE (no quicklisp, no kernel) break include-book?
;;;
;;; Usage:  /home/acl2/saved_acl2 < test-save-bare.lisp
;;; Then:   ./test-bare-image

;; Exit LP
(value :q)
(sb-ext:disable-debugger)

(format t "~%Saving bare image...~%")

(save-exec "/workspaces/acl2-jupyter-stp/context/acl2-jupyter-kernel/test-bare-image" nil
           :init-forms '((set-raw-mode-on!)
                         (format t "~%=== include-book after bare save-exec ===~%")
                         (handler-case
                             (progn
                               (include-book "std/lists/append" :dir :system)
                               (cw "BARE: SUCCESS~%"))
                           (serious-condition (c)
                             (format t "BARE: SERIOUS: ~A~%" c)))
                         (value :q)))
