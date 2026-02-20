;;; Test if loading our kernel system breaks include-book.
;;;
;;; Usage:  /home/acl2/saved_acl2 < test-kernel-load-include-book.lisp

;; Exit LP to raw Lisp
(value :q)
(sb-ext:disable-debugger)

;; Load quicklisp + our kernel system (same as build-kernel-image.sh)
(load "/home/jovyan/quicklisp/setup.lisp")
(ql:quickload :acl2-jupyter-kernel :silent t)
(format t "~%Kernel system loaded.~%")

;; Re-enter LP
(lp)

;; Now test include-book inside LP
(include-book "std/lists/append" :dir :system)
(cw "KERNEL-LOAD-INCLUDE-BOOK: SUCCESS~%")
(value :q)
(sb-ext:exit :code 0)
