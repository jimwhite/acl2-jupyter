;;; Test if quicklisp loading breaks include-book.
;;;
;;; This loads quicklisp into saved_acl2 (same as build-kernel-image.sh)
;;; but does NOT load our kernel system. Then tests include-book.
;;;
;;; Usage:  /home/acl2/saved_acl2 < test-quicklisp-include-book.lisp

;; Exit LP to raw Lisp
(value :q)
(sb-ext:disable-debugger)

;; Load quicklisp (same as build-kernel-image.sh)
(load "/home/jovyan/quicklisp/setup.lisp")
(format t "~%Quicklisp loaded.~%")

;; Re-enter LP
(lp)

;; Now test include-book inside LP
(include-book "std/lists/append" :dir :system)
(cw "QUICKLISP-INCLUDE-BOOK: SUCCESS~%")
(value :q)
(sb-ext:exit :code 0)
